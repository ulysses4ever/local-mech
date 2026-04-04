(* LoCalSafety.v — Type safety for LoCal (thesis §2.2.3, Appendix A)
   Defines store well-formedness and states the main type safety theorems:
     • Progress   — well-typed expressions are values or can step (PROVED)
     • Preservation — stepping preserves typing and well-formedness
     • Type Safety — well-typed programs never get stuck *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From LocalMech Require Import LoCalSyntax.
From LocalMech Require Import LoCalStatic.
From LocalMech Require Import LoCalDynamic.

Import LoCalSyntax.LoCalSyntax.
Import LoCalStatic.LoCalStatic.
Import LoCalDynamic.LoCalDynamic.

Module LoCalSafety.

Open Scope string_scope.

(* ================================================================= *)
(* Helper:  allocptr — highest allocated index in a region            *)
(*                                                                    *)
(*   allocptr(r, S) = max({−1} ∪ {j | S(r)(j) exists})              *)
(*                                                                    *)
(* Returns None when the region is absent or its heap is empty;       *)
(* this stands for −1 (no allocation yet).                            *)
(* ================================================================= *)

Fixpoint max_heap_index (h : heap) : option nat :=
  match h with
  | nil => None
  | (i, _) :: h' =>
      match max_heap_index h' with
      | None => Some i
      | Some j => Some (Nat.max i j)
      end
  end.

Definition allocptr (S : store) (r : region_var) : option nat :=
  match store_find_heap S r with
  | None => None
  | Some h => max_heap_index h
  end.

(* "i > allocptr(r, S)":
   when allocptr is None (no allocations), any nat i satisfies this. *)
Definition gt_allocptr (i : nat) (ap : option nat) : Prop :=
  match ap with
  | None => True
  | Some k => i > k
  end.

(* ================================================================= *)
(* Constructor-application well-formedness                            *)
(*   C ⊢_{wf_cfc}  M ; S                                            *)
(* (thesis §2.2.3 — well-formedness of in-flight constructors)       *)
(* ================================================================= *)

Definition constr_app_wf
    (DI : datacon_info)
    (C  : conloc_env)
    (M  : loc_map)
    (S  : store) : Prop :=

  (* Rule 1 — constraint-start:
     (l^r ↦ start(r)) ∈ C  ⟹  M(l^r) = ⟨r, 0⟩ *)
  (forall l r,
    In ((l, r), LE_Start r) C ->
    lookup_loc M (l, r) = Some (r, 0))
  /\
  (* Rule 2 — constraint-tag:
     (l^r ↦ l'^r + 1) ∈ C  ⟹
       ∃ i, M(l'^r) = ⟨r, i⟩  ∧  M(l^r) = ⟨r, i+1⟩ *)
  (forall l r l',
    In ((l, r), LE_Next l' r) C ->
    exists i,
      lookup_loc M (l', r) = Some (r, i) /\
      lookup_loc M (l, r) = Some (r, i + 1))
  /\
  (* Rule 3 — constraint-after:
     (l^r ↦ after(T@l'^r)) ∈ C  ⟹
       ∃ i j, M(l'^r) = ⟨r,i⟩ ∧ ewitness(T,⟨r,i⟩,S,⟨r,j⟩)
              ∧ M(l^r) = ⟨r,j⟩ *)
  (forall l r T l',
    In ((l, r), LE_After T l' r) C ->
    exists i j,
      lookup_loc M (l', r) = Some (r, i) /\
      end_witness DI S (r, i) T (r, j) /\
      lookup_loc M (l, r) = Some (r, j)).

(* ================================================================= *)
(* Allocation well-formedness                                         *)
(*   A ; N ⊢_{wf_ca}  M ; S                                         *)
(* (thesis §2.2.3 — write-once / linear-allocation invariant)        *)
(* ================================================================= *)

Definition alloc_wf
    (DI : datacon_info)
    (A  : alloc_env)
    (N  : nursery)
    (M  : loc_map)
    (S  : store) : Prop :=

  (* Rule 1 — linear-alloc (in-flight):
     (r ↦ (l,r)) ∈ A  ∧  (l,r) ∈ N  ⟹
       ∃ i, M(l,r) = ⟨r,i⟩  ∧  i > allocptr(r,S) *)
  (forall r l,
    In (r, AP_Loc (l, r)) A ->
    In (l, r) N ->
    exists i,
      lookup_loc M (l, r) = Some (r, i) /\
      gt_allocptr i (allocptr S r))
  /\
  (* Rule 2 — linear-alloc2 (fully allocated):
     (r ↦ (l,r)) ∈ A  ∧  M(l,r) = ⟨r,i⟩  ∧  (l,r) ∉ N
       ∧  ewitness(T,⟨r,i⟩,S,⟨r,j⟩)
       ⟹  j > allocptr(r,S) *)
  (forall r l i T j,
    In (r, AP_Loc (l, r)) A ->
    lookup_loc M (l, r) = Some (r, i) ->
    ~ In (l, r) N ->
    end_witness DI S (r, i) T (r, j) ->
    gt_allocptr j (allocptr S r))
  /\
  (* Rule 3 — write-once:
     (l,r) ∈ N  ⟹  ∃ i, M(l,r) = ⟨r,i⟩  ∧  S(r)(i) = None *)
  (forall l r,
    In (l, r) N ->
    exists i,
      lookup_loc M (l, r) = Some (r, i) /\
      heap_lookup S r i = None)
  /\
  (* Rule 4 — empty-region:
     (r ↦ ∅) ∈ A  ⟹  r ∉ dom(S) *)
  (forall r,
    In (r, AP_None) A ->
    store_find_heap S r = None)
  /\
  (* Rule 5 — store-region-scoped:
     any region with allocated cells is tracked by A with a current focus. *)
  (forall r,
    store_find_heap S r <> None ->
    exists l, In (r, AP_Loc (l, r)) A).

(* ================================================================= *)
(* Store well-formedness  (main judgment)                             *)
(*   Σ ; C ; A ; N  ⊢_wf  M ; S                                    *)
(* (thesis §2.2.3, Definition)                                       *)
(* ================================================================= *)

Definition store_wf
    (DI    : datacon_info)
    (Sigma : store_type)
    (C     : conloc_env)
    (A     : alloc_env)
    (N     : nursery)
    (M     : loc_map)
    (S     : store) : Prop :=

  (* Rule 1 — map-store consistency:
     ∀ (l,r) ↦ T ∈ Σ,
       ∃ i j, M(l,r) = ⟨r,i⟩ ∧ ewitness(T, ⟨r,i⟩, S, ⟨r,j⟩) *)
  (forall l r T,
    In ((l, r), T) Sigma ->
    exists i j,
      lookup_loc M (l, r) = Some (r, i) /\
      end_witness DI S (r, i) T (r, j))
  /\
  (* Rule 2 — constructor-application well-formedness *)
  constr_app_wf DI C M S
  /\
  (* Rule 3 — allocation well-formedness *)
  alloc_wf DI A N M S
  /\
  (* Rule 4 — dom(Σ) ∩ N = ∅ *)
  (forall l r T,
    In ((l, r), T) Sigma -> ~ In (l, r) N)
  /\
  (forall l r,
    In (l, r) N ->
    ~ exists T, In ((l, r), T) Sigma).

(* ================================================================= *)
(* In_lookup_fdecl: membership in the function list implies lookup    *)
(* succeeds (needed to bridge typing's In-premise with step's        *)
(* lookup_fdecl call).                                                *)
(* ================================================================= *)

Lemma In_lookup_fdecl :
  forall FDs f locs params retty regions body,
    In (FunDecl f locs params retty regions body) FDs ->
    exists l' p' t' rg' b',
      lookup_fdecl FDs f = Some (FunDecl f l' p' t' rg' b').
Proof.
  induction FDs as [| [f0 l0 p0 t0 rg0 b0] FDs' IH];
    intros f locs params retty regions body Hin.
  - inversion Hin.
  - simpl. destruct (fun_var_eq_dec f f0).
    + subst. do 5 eexists. reflexivity.
    + destruct Hin as [Heq | Hin].
      * inversion Heq; subst. congruence.
      * eapply IH. exact Hin.
Qed.

(* ================================================================= *)
(* Additional invariants needed for progress                          *)
(* ================================================================= *)

(* Each constructor maps to unique info in DI. *)
Definition di_functional (DI : datacon_info) : Prop :=
  forall K info1 info2,
    In (K, info1) DI -> In (K, info2) DI -> info1 = info2.

(* Concrete location values are consistent with the location map. *)
Definition val_wf (M : loc_map) (vl : val) : Prop :=
  match vl with
  | v_var _ => True
  | v_cloc r0 i l r => lookup_loc M (l, r) = Some (r0, i)
  end.

(* All concrete location values in an expression are consistent. *)
Fixpoint expr_wf (M : loc_map) (e : expr) {struct e} : Prop :=
  match e with
  | e_val vl => val_wf M vl
  | e_app _ _ vs => Forall (val_wf M) vs
  | e_datacon _ _ _ vs => Forall (val_wf M) vs
  | e_let _ _ e1 e2 => expr_wf M e1 /\ expr_wf M e2
  | e_letloc _ _ _ body => expr_wf M body
  | e_letregion _ body => expr_wf M body
  | e_case vl pats =>
      val_wf M vl /\
      (let fix pats_wf (ps : list pat) : Prop :=
        match ps with
        | nil => True
        | pat_clause _ _ body :: ps' => expr_wf M body /\ pats_wf ps'
        end
      in pats_wf pats)
  end.

(* ================================================================= *)
(* Helper lemmas for progress                                         *)
(* ================================================================= *)

Lemma lookup_datacon_In : forall DI K info,
  lookup_datacon DI K = Some info -> In (K, info) DI.
Proof.
  induction DI as [|[K' info'] DI' IH]; intros; simpl in *.
  - discriminate.
  - destruct (datacon_eq_dec K K').
    + inversion H; subst. left; reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma In_find_matching_pat : forall K pats binds body,
  In (pat_clause K binds body) pats ->
  exists binds' body',
    find_matching_pat K pats = Some (pat_clause K binds' body').
Proof.
  intros K pats. induction pats as [|[K' b' bd'] pats' IH];
    intros binds body Hin.
  - destruct Hin.
  - simpl. destruct (datacon_eq_dec K K') as [Heq|Hneq].
    + subst K'. eauto.
    + destruct Hin as [Hin | Hin].
      * inversion Hin; subst. congruence.
      * eapply IH. exact Hin.
Qed.

Lemma find_matching_pat_In : forall K pats p,
  find_matching_pat K pats = Some p -> In p pats.
Proof.
  induction pats as [|[K' b' bd'] pats' IH]; intros; simpl in *.
  - discriminate.
  - destruct (datacon_eq_dec K K') as [Heq|Hneq].
    + inversion H; subst. left; reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma ewf_to_field_starts : forall DI St r i Ts j,
  end_witness_fields DI St r i Ts j ->
  exists indices, field_starts DI St r i Ts indices.
Proof.
  intros. induction H.
  - exists nil. constructor.
  - destruct IHend_witness_fields as [idx Hfs].
    eexists (_ :: _). econstructor; eassumption.
Qed.

Lemma pats_have_type_In :
  forall FDs DI tc_s G S0 C pats p Al Nl A2 N2 t,
    pats_have_type FDs DI tc_s G S0 C Al Nl A2 N2 t pats ->
    In p pats ->
    exists A1 N1 A3 N3,
      pat_has_type FDs DI tc_s G S0 C A1 N1 A3 N3 t p.
Proof.
  intros FE0 DI0 tc_s0 G0 S0' C0.
  induction pats as [|p' ps' IH]; intros p0 Al0 Nl0 A20 N20 t0 Hpats Hin.
  - inversion Hpats. destruct Hin.
  - inversion Hpats; subst.
    destruct Hin as [Heq | Hin2].
    + subst. eauto.
    + eapply IH. exact H13. exact Hin2.
Qed.

Lemma pat_has_type_inv :
  forall FDs DI tc_s G S0 C Al Nl A2 N2 t dc binds body,
    pat_has_type FDs DI tc_s G S0 C Al Nl A2 N2 t
                      (pat_clause dc binds body) ->
    exists tc fieldtcs,
      In (dc, (tc, fieldtcs)) DI /\ tc = tc_s /\
      pat_field_tycons binds = fieldtcs.
Proof.
  intros. inversion H; subst. eauto.
Qed.

Definition tenv_equiv (G1 G2 : type_env) : Prop :=
  forall x, lookup_tenv G1 x = lookup_tenv G2 x.

Definition store_extends (Sigma Sigma' : store_type) : Prop :=
  forall lr tc, In (lr, tc) Sigma -> In (lr, tc) Sigma'.

Definition conloc_extends (C C' : conloc_env) : Prop :=
  forall lr le, In (lr, le) C -> In (lr, le) C'.

Lemma store_extends_refl :
  forall Sigma,
    store_extends Sigma Sigma.
Proof.
  unfold store_extends. auto.
Qed.

Lemma conloc_extends_refl :
  forall C,
    conloc_extends C C.
Proof.
  unfold conloc_extends. auto.
Qed.

Lemma in_remove_alloc_region_preserved :
  forall A r r' ap',
    In (r', ap') A ->
    r' <> r ->
    In (r', ap') (remove_alloc_region A r).
Proof.
  intros A r r' ap' Hin Hneq.
  unfold remove_alloc_region.
  induction A as [| [ra apa] A IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst.
      destruct (region_var_eq_dec r' r).
      * contradiction.
      * simpl. left. reflexivity.
    + destruct (region_var_eq_dec ra r).
      * apply IH; assumption.
      * simpl. right. apply IH; assumption.
Qed.

Lemma in_remove_alloc_region_inv :
  forall A r r' ap',
    In (r', ap') (remove_alloc_region A r) ->
    In (r', ap') A /\ r' <> r.
Proof.
  induction A as [| [ra apa] A IH]; intros r r' ap' Hin; simpl in Hin.
  - contradiction.
  - destruct (region_var_eq_dec ra r).
    + destruct (IH _ _ _ Hin) as [HinA Hneq].
      split.
      * right. exact HinA.
      * exact Hneq.
    + destruct Hin as [Heq | Hin].
      * inversion Heq; subst.
        split.
        -- left. reflexivity.
        -- exact n.
      * destruct (IH _ _ _ Hin) as [HinA Hneq].
        split.
        -- right. exact HinA.
        -- exact Hneq.
Qed.

Lemma in_extend_alloc_new :
  forall A r ap,
    In (r, ap) (extend_alloc A r ap).
Proof.
  intros A r ap. unfold extend_alloc. simpl. left. reflexivity.
Qed.

Lemma in_extend_alloc_old :
  forall A r ap r' ap',
    In (r', ap') A ->
    r' <> r ->
    In (r', ap') (extend_alloc A r ap).
Proof.
  intros A r ap r' ap' Hin Hneq.
  unfold extend_alloc. simpl. right.
  apply in_remove_alloc_region_preserved; assumption.
Qed.

Lemma in_extend_nursery_inv :
  forall N lr lr',
    In lr' (extend_nursery N lr) ->
    lr' = lr \/ In lr' N.
Proof.
  intros N lr lr' Hin.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - left. symmetry. exact Heq.
  - right. exact Hin.
Qed.

Lemma not_in_extend_nursery_inv :
  forall N lr lr',
    ~ In lr' (extend_nursery N lr) ->
    lr' <> lr /\ ~ In lr' N.
Proof.
  intros N lr lr' Hnin.
  split.
  - intro Heq. apply Hnin. simpl. left. symmetry. exact Heq.
  - intro Hin. apply Hnin. simpl. right. exact Hin.
Qed.

Lemma fresh_region_store_absent :
  forall DI A N M S r,
    alloc_wf DI A N M S ->
    fresh_region A r ->
    store_find_heap S r = None.
Proof.
  intros DI A N M S r Halloc Hfresh.
  destruct Halloc as [_ [_ [_ [Hempty Htracked]]]].
  destruct (store_find_heap S r) eqn:Hheap; auto.
  exfalso.
  assert (Hheap_ne : store_find_heap S r <> None).
  { rewrite Hheap. discriminate. }
  destruct (Htracked r Hheap_ne) as [l Hin].
  exact (Hfresh (AP_Loc (l, r)) Hin).
Qed.

Definition subst_pat_val (x : term_var) (s : val) (p : pat) : pat :=
  match p with
  | pat_clause K binds body =>
      if existsb
           (fun b => if term_var_eq_dec x (fst b) then true else false)
           binds
      then pat_clause K binds body
      else pat_clause K binds (subst_val x s body)
  end.

Fixpoint subst_pats_val (x : term_var) (s : val) (ps : list pat) : list pat :=
  match ps with
  | nil => nil
  | p :: ps' => subst_pat_val x s p :: subst_pats_val x s ps'
  end.

Lemma lookup_tenv_app :
  forall G1 G2 x,
    lookup_tenv ((G1 ++ G2)%list) x =
    match lookup_tenv G1 x with
    | Some t => Some t
    | None => lookup_tenv G2 x
    end.
Proof.
  induction G1 as [| [y t] G1 IH]; intros G2 x; simpl.
  - reflexivity.
  - destruct (term_var_eq_dec x y); auto.
Qed.

Lemma in_lookup_tenv :
  forall G x t,
    In (x, t) G ->
    exists t', lookup_tenv G x = Some t'.
Proof.
  induction G as [| [y u] G IH]; intros x t Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst.
      destruct (term_var_eq_dec x x); [eexists; reflexivity | contradiction].
    + destruct (term_var_eq_dec x y).
      * eexists; reflexivity.
      * apply IH in Hin as [t' Hlk]. exists t'. exact Hlk.
Qed.

Lemma extend_tenv_list_rev :
  forall G binds,
    extend_tenv_list G binds = (rev binds ++ G)%list.
Proof.
  intros G binds. revert G.
  induction binds as [| b binds IH]; intros G; simpl.
  - reflexivity.
  - rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma extend_tenv_list_app :
  forall prefix G binds,
    extend_tenv_list (prefix ++ G)%list binds =
    (((rev binds ++ prefix)%list) ++ G)%list.
Proof.
  intros prefix G binds.
  rewrite extend_tenv_list_rev.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma tenv_equiv_extend :
  forall G1 G2 x t,
    tenv_equiv G1 G2 ->
    tenv_equiv (extend_tenv G1 x t) (extend_tenv G2 x t).
Proof.
  unfold tenv_equiv, extend_tenv.
  intros G1 G2 x t Heq y. simpl.
  destruct (term_var_eq_dec y x); auto.
Qed.

Lemma tenv_equiv_extend_list :
  forall G1 G2 binds,
    tenv_equiv G1 G2 ->
    tenv_equiv (extend_tenv_list G1 binds) (extend_tenv_list G2 binds).
Proof.
  intros G1 G2 binds Heq. revert G1 G2 Heq.
  induction binds as [| b binds IH]; intros G1 G2 Heq; simpl.
  - exact Heq.
  - destruct b as [x t]. apply IH. apply tenv_equiv_extend. exact Heq.
Qed.

Lemma tenv_equiv_extend_shadow :
  forall G x t1 t2,
    tenv_equiv (extend_tenv (extend_tenv G x t2) x t1)
               (extend_tenv G x t1).
Proof.
  unfold tenv_equiv, extend_tenv.
  intros G x t1 t2 y. simpl.
  destruct (term_var_eq_dec y x); auto.
Qed.

Lemma tenv_equiv_shadow_under_prefix :
  forall prefix G x t,
    lookup_tenv prefix x <> None ->
    tenv_equiv ((prefix ++ (x, t) :: G)%list) ((prefix ++ G)%list).
Proof.
  unfold tenv_equiv.
  intros prefix G x t Hprefix y.
  rewrite !lookup_tenv_app.
  destruct (lookup_tenv prefix y) eqn:Hlookup; auto.
  simpl.
  destruct (term_var_eq_dec y x) as [Heq | Hneq].
  - subst. exfalso. apply Hprefix. exact Hlookup.
  - destruct (term_var_eq_dec y x); [contradiction | reflexivity].
Qed.

Lemma closed_value_typing_any_context :
  forall FDs DI Sigma C A N vl T,
    has_type FDs DI nil Sigma C A N A N (e_val vl) T ->
    forall G Sigma' C' A' N',
      (forall lr tc, In (lr, tc) Sigma -> In (lr, tc) Sigma') ->
      has_type FDs DI G Sigma' C' A' N' A' N' (e_val vl) T.
Proof.
  intros FDs DI Sigma C A N vl T Hv.
  inversion Hv; subst; intros G Sigma' C' A' N' Hsigma.
  - match goal with [ Hlookup : lookup_tenv nil _ = Some _ |- _ ] =>
      simpl in Hlookup; discriminate
    end.
  - econstructor. eauto.
Qed.

Lemma value_typing_any_context :
  forall FDs DI G Sigma C A N vl T,
    has_type FDs DI G Sigma C A N A N (e_val vl) T ->
    forall G' Sigma' C' A' N',
      tenv_equiv G G' ->
      (forall lr tc, In (lr, tc) Sigma -> In (lr, tc) Sigma') ->
      has_type FDs DI G' Sigma' C' A' N' A' N' (e_val vl) T.
Proof.
  intros FDs DI G Sigma C A N vl T Hty.
  inversion Hty; subst; intros G' Sigma' C' A' N' Heq Hsigma.
  - apply T_Var.
    + match goal with
      | [ Hlk : lookup_tenv G x = Some _ |- _ ] =>
          rewrite <- (Heq x); exact Hlk
      end.
    + match goal with
      | [ Hstore : In ((l, r), tc) Sigma |- _ ] => apply Hsigma; exact Hstore
      end.
  - apply T_ConcreteLoc.
    match goal with
    | [ Hstore : In ((l, r), tc) Sigma |- _ ] => apply Hsigma; exact Hstore
    end.
Qed.

Lemma has_type_value_same_io :
  forall FDs DI G Sigma C A N A' N' vl T,
    has_type FDs DI G Sigma C A N A' N' (e_val vl) T ->
    A' = A /\ N' = N.
Proof.
  intros FDs DI G Sigma C A N A' N' vl T Hty.
  inversion Hty; subst; auto.
Qed.

Scheme has_type_ind' := Induction for has_type Sort Prop
with field_vals_have_type_ind' := Induction for field_vals_have_type Sort Prop
with app_vals_have_type_ind' := Induction for app_vals_have_type Sort Prop
with pat_has_type_ind' := Induction for pat_has_type Sort Prop
with pats_have_type_ind' := Induction for pats_have_type Sort Prop.

Combined Scheme typing_mutind
  from has_type_ind', pat_has_type_ind', pats_have_type_ind'.

(* The thesis treats fresh location/region binders as an implicit
   side-condition.  We keep the typing rules monotone, and instead
   expose the needed binder-freshness obligations as a separate
   proof-side judgment that mirrors the typing derivation shape. *)
Inductive has_type_fresh :
  fun_env -> datacon_info ->
  type_env -> store_type -> conloc_env ->
  alloc_env -> nursery ->
  alloc_env -> nursery ->
  expr -> located_type -> Prop :=
  | TF_Var :
      forall FDs DI G Sigma C A N x tc l r,
        has_type_fresh FDs DI G Sigma C A N A N
                       (e_val (v_var x)) (LocTy tc l r)
  | TF_ConcreteLoc :
      forall FDs DI G Sigma C A N r0 i l r tc,
        has_type_fresh FDs DI G Sigma C A N A N
                       (e_val (v_cloc r0 i l r)) (LocTy tc l r)
  | TF_Let :
      forall FDs DI G Sigma C A N A' N' A'' N''
             x e1 e2 tc1 l1 r1 tc2 l2 r2,
        has_type_fresh FDs DI G Sigma C A N A' N' e1 (LocTy tc1 l1 r1) ->
        has_type_fresh FDs DI (extend_tenv G x (LocTy tc1 l1 r1))
                       (extend_store Sigma (l1, r1) tc1)
                       C A' N' A'' N'' e2 (LocTy tc2 l2 r2) ->
        has_type_fresh FDs DI G Sigma C A N A'' N''
                       (ELet x (LocTy tc1 l1 r1) e1 e2) (LocTy tc2 l2 r2)
  | TF_LRegion :
      forall FDs DI G Sigma C A N A' N' r e t,
        fresh_region A r ->
        has_type_fresh FDs DI G Sigma C (extend_alloc A r AP_None) N A' N' e t ->
        has_type_fresh FDs DI G Sigma C A N A' N' (e_letregion r e) t
  | TF_LLStart :
      forall FDs DI G Sigma C A N A'' N'' l r e tc' l' r',
        letloc_fresh_ctx Sigma C A N (l, r) ->
        has_type_fresh FDs DI G Sigma
                       (extend_conloc C (l, r) (LE_Start r))
                       (extend_alloc A r (AP_Loc (l, r)))
                       (extend_nursery N (l, r))
                       A'' N'' e (LocTy tc' l' r') ->
        has_type_fresh FDs DI G Sigma C A N A'' N''
                       (e_letloc l r (LE_Start r) e) (LocTy tc' l' r')
  | TF_LLTag :
      forall FDs DI G Sigma C A N A'' N'' l lprev r e tc'' l'' r'',
        letloc_fresh_ctx Sigma C A N (l, r) ->
        has_type_fresh FDs DI G Sigma
                       (extend_conloc C (l, r) (LE_Next lprev r))
                       (extend_alloc A r (AP_Loc (l, r)))
                       (extend_nursery N (l, r))
                       A'' N'' e (LocTy tc'' l'' r'') ->
        has_type_fresh FDs DI G Sigma C A N A'' N''
                       (e_letloc l r (LE_Next lprev r) e) (LocTy tc'' l'' r'')
  | TF_LLAfter :
      forall FDs DI G Sigma C A N A'' N'' l l1 r tc_prev e tc' l' r',
        letloc_fresh_ctx Sigma C A N (l, r) ->
        has_type_fresh FDs DI G Sigma
                       (extend_conloc C (l, r) (LE_After tc_prev l1 r))
                       (extend_alloc A r (AP_Loc (l, r)))
                       (extend_nursery N (l, r))
                       A'' N'' e (LocTy tc' l' r') ->
        has_type_fresh FDs DI G Sigma C A N A'' N''
                       (e_letloc l r (LE_After tc_prev l1 r) e) (LocTy tc' l' r')
  | TF_DataCon :
      forall FDs DI G Sigma C A N dc l r vs tc
             (fieldtcs : list tycon) (fields : list field_layout_entry),
        has_type_fresh FDs DI G Sigma C A N
                       (extend_alloc A r (AP_Loc (l, r)))
                       (remove_nursery N (l, r))
                       (e_datacon dc l r vs) (LocTy tc l r)
  | TF_App :
      forall FDs DI G Sigma C A N f lrs vs tc l r
             (f_locs : list (loc_var * region_var))
             (f_params : list (term_var * ty))
             (f_retty : ty)
             (f_regions : list region_var)
             (f_body : expr),
        has_type_fresh FDs DI G Sigma C A N A
                       (remove_nursery N (l, r))
                       (e_app f lrs vs) (LocTy tc l r)
  | TF_Case :
      forall FDs DI G Sigma C A N A' N' scrut ps tc_s
             (l_s : loc_var) (r_s : region_var) t,
        pats_have_type_fresh FDs DI tc_s G Sigma C A N A' N' t ps ->
        has_type_fresh FDs DI G Sigma C A N A' N'
                       (e_case scrut ps) t

with pat_has_type_fresh :
  fun_env -> datacon_info ->
  tycon -> type_env -> store_type -> conloc_env ->
  alloc_env -> nursery ->
  alloc_env -> nursery ->
  located_type -> pat -> Prop :=
  | TF_Pat :
      forall FDs DI tc_s G Sigma C A N A' N'
             dc binds body (tc : tycon) (fieldtcs : list tycon)
             (tc_res : tycon) (l : loc_var) (r : region_var),
        has_type_fresh FDs DI
                       (extend_tenv_list G binds)
                       (extend_store_list Sigma (pat_store_entries binds))
                       C A N A' N' body (LocTy tc_res l r) ->
        pat_has_type_fresh FDs DI tc_s G Sigma C A N A' N'
                           (LocTy tc_res l r) (pat_clause dc binds body)

with pats_have_type_fresh :
  fun_env -> datacon_info ->
  tycon -> type_env -> store_type -> conloc_env ->
  alloc_env -> nursery ->
  alloc_env -> nursery ->
  located_type -> list pat -> Prop :=
  | TF_PatsNil :
      forall FDs DI tc_s G Sigma C A N t,
        pats_have_type_fresh FDs DI tc_s G Sigma C A N A N t nil
  | TF_PatsCons :
      forall FDs DI tc_s G Sigma C A N A1 N1 A2 N2 t p ps,
        pat_has_type_fresh FDs DI tc_s G Sigma C A N A1 N1 t p ->
        pats_have_type_fresh FDs DI tc_s G Sigma C A1 N1 A2 N2 t ps ->
        pats_have_type_fresh FDs DI tc_s G Sigma C A N A2 N2 t (cons p ps).

Scheme has_type_fresh_ind' := Induction for has_type_fresh Sort Prop
with pat_has_type_fresh_ind' := Induction for pat_has_type_fresh Sort Prop
with pats_have_type_fresh_ind' := Induction for pats_have_type_fresh Sort Prop.

Lemma lookup_loc_extend_eq :
  forall M lr cl,
    lookup_loc (extend_loc M lr cl) lr = Some cl.
Proof.
  intros M lr cl.
  unfold extend_loc. simpl.
  destruct (laddr_eq_dec lr lr); congruence.
Qed.

Lemma lookup_loc_extend_neq :
  forall M lr1 lr2 cl,
    lr1 <> lr2 ->
    lookup_loc (extend_loc M lr2 cl) lr1 = lookup_loc M lr1.
Proof.
  intros M lr1 lr2 cl Hneq.
  unfold extend_loc. simpl.
  destruct (laddr_eq_dec lr1 lr2); congruence.
Qed.

Lemma in_store_laddrs_of_entry :
  forall Sigma lr tc,
    In (lr, tc) Sigma ->
    In lr (store_laddrs Sigma).
Proof.
  induction Sigma as [| [lr' tc'] Sigma IH]; intros lr tc Hin.
  - inversion Hin.
  - simpl in *. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl. left. reflexivity.
    + simpl. right. eapply IH. exact Hin.
Qed.

Lemma in_conloc_support_of_key :
  forall C lr le,
    In (lr, le) C ->
    In lr (conloc_support C).
Proof.
  induction C as [| [lr' le'] C IH]; intros lr le Hin.
  - inversion Hin.
  - simpl in *. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl. left. reflexivity.
    + simpl. right. apply in_or_app. right. eapply IH. exact Hin.
Qed.

Lemma in_conloc_support_of_rhs :
  forall C lr lr' le,
    In (lr', le) C ->
    In lr (locexp_laddrs le) ->
    In lr (conloc_support C).
Proof.
  induction C as [| [lr0 le0] C IH]; intros lr lr' le HinC HinLe.
  - inversion HinC.
  - simpl in *. destruct HinC as [Heq | HinC].
    + inversion Heq; subst. simpl. right. apply in_or_app. left. exact HinLe.
    + simpl. right. apply in_or_app. right.
      apply IH with (lr' := lr') (le := le); assumption.
Qed.

Lemma in_alloc_laddrs_of_entry :
  forall A r lr,
    In (r, AP_Loc lr) A ->
    In lr (alloc_laddrs A).
Proof.
  induction A as [| [r' ap] A IH]; intros r lr Hin.
  - inversion Hin.
  - simpl in *. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl. left. reflexivity.
    + destruct ap; simpl.
      * eapply IH. exact Hin.
      * right. eapply IH. exact Hin.
Qed.

Lemma max_heap_index_none_nil :
  forall h,
    max_heap_index h = None ->
    h = nil.
Proof.
  induction h as [| [i K] h IH]; intros Hmax.
  - reflexivity.
  - simpl in Hmax. destruct (max_heap_index h); discriminate.
Qed.

Lemma heap_find_gt_max_none :
  forall h i k,
    max_heap_index h = Some k ->
    i > k ->
    heap_find h i = None.
Proof.
  induction h as [| [j K] h IH]; intros i k Hmax Hgt.
  - inversion Hmax.
  - simpl in Hmax.
    destruct (max_heap_index h) as [k'|] eqn:Hmax_tl.
    + inversion Hmax; subst k. simpl.
      assert (Hij : i <> j) by lia.
      destruct (Nat.eqb i j) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction|].
      apply (IH i k').
      * reflexivity.
      * lia.
    + apply max_heap_index_none_nil in Hmax_tl. subst h.
      inversion Hmax; subst k. simpl.
      assert (Hij : i <> j) by lia.
      destruct (Nat.eqb i j) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction|].
      reflexivity.
Qed.

Lemma gt_allocptr_heap_lookup_none :
  forall S r i,
    gt_allocptr i (allocptr S r) ->
    heap_lookup S r i = None.
Proof.
  intros S r i Hgt.
  unfold allocptr, heap_lookup in *.
  destruct (store_find_heap S r) as [h|] eqn:Hheap; simpl in *.
  - destruct (max_heap_index h) as [k|] eqn:Hmax.
    + eapply heap_find_gt_max_none; eauto.
    + apply max_heap_index_none_nil in Hmax. subst h. reflexivity.
  - reflexivity.
Qed.

Lemma gt_allocptr_succ :
  forall i ap,
    gt_allocptr i ap ->
    gt_allocptr (i + 1) ap.
Proof.
  intros i ap Hgt.
  destruct ap as [k|]; simpl in *.
  - lia.
  - exact I.
Qed.

Lemma has_type_tenv_equiv :
  (forall FDs DI G Sigma C A N A' N' e T,
      has_type FDs DI G Sigma C A N A' N' e T ->
      forall G', tenv_equiv G G' ->
      has_type FDs DI G' Sigma C A N A' N' e T)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T p,
      pat_has_type FDs DI tc_s G Sigma C A N A' N' T p ->
      forall G', tenv_equiv G G' ->
      pat_has_type FDs DI tc_s G' Sigma C A N A' N' T p)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T ps,
      pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps ->
      forall G', tenv_equiv G G' ->
      pats_have_type FDs DI tc_s G' Sigma C A N A' N' T ps).
Proof.
  eapply typing_mutind
    with
      (P0 := fun FDs DI G Sigma C A N r vs fields HT =>
               forall G', tenv_equiv G G' ->
                 field_vals_have_type FDs DI G' Sigma C A N r vs fields)
      (P1 := fun FDs DI G Sigma C A N formals actuals vs params HT =>
               forall G', tenv_equiv G G' ->
                 app_vals_have_type FDs DI G' Sigma C A N formals actuals vs params).
  - intros FDs DI G S0 C A N x tc l r Hlookup Hstore G' Heq.
    apply T_Var.
    + rewrite <- (Heq x). exact Hlookup.
    + exact Hstore.
  - intros FDs DI G S0 C A N r0 i l r tc Hstore G' Heq.
    apply T_ConcreteLoc. exact Hstore.
  - intros FDs DI G S0 C A N A' N' A'' N'' x e1 e2 tc1 l1 r1 tc2 l2 r2
      Hty1 IH1 Hty2 IH2 G' Heq.
    eapply T_Let.
    + apply IH1. exact Heq.
    + apply IH2. apply tenv_equiv_extend. exact Heq.
  - intros FDs DI G S0 C A N A' N' r e t Hfresh Hty IH G' Heq.
    eapply T_LRegion; eauto.
  - intros FDs DI G S0 C A N A'' N'' l r e tc' l' r'
      Halloc HfreshOut Hneq Hty IH G' Heq.
    eapply T_LLStart; eauto.
  - intros FDs DI G S0 C A N A'' N'' l lprev r e tc'' l'' r''
      Halloc Hnur HfreshOut Hneq Hty IH G' Heq.
    eapply T_LLTag; eauto.
  - intros FDs DI G S0 C A N A'' N'' l l1 r tc_prev e tc' l' r'
      Halloc Hstore Hnotin HfreshOut Hneq
      Hty IH G' Heq.
    eapply T_LLAfter; eauto.
  - intros FDs DI G S0 C A N dc l r vs tc fieldtcs fields
      Hdc Hnur Hfields Hlayout Hfocus Hvals IHvals G' Heq.
    eapply T_DataCon; eauto.
  - intros FDs DI G S0 C A N f lrs vs tc l r f_locs f_params f_retty
      f_regions f_body Hfd Hnur Halloc Hlen1 Hlen2 Hargs IHargs G' Heq.
    eapply T_App; eauto.
  - intros FDs DI G S0 C A N A' N' scrut ps tc_s l_s r_s t
      Hscrut IHscrut Hcover Hps IHps G' Heq.
    eapply T_Case.
    + apply IHscrut. exact Heq.
    + exact Hcover.
    + apply IHps. exact Heq.
  - intros FDs DI G S0 C A N r G' Heq.
    exact (T_FieldValsNil FDs DI G' S0 C A N r).
  - intros FDs DI G S0 C A N r vl fld vs flds Hhead IHhead Htail IHtail G' Heq.
    eapply T_FieldValsCons.
    + apply IHhead. exact Heq.
    + apply IHtail. exact Heq.
  - intros FDs DI G S0 C A N formals actuals G' Heq.
    exact (T_AppValsNil FDs DI G' S0 C A N formals actuals).
  - intros FDs DI G S0 C A N formals actuals vl param vs params
      Hhead IHhead Htail IHtail G' Heq.
    eapply T_AppValsCons.
    + apply IHhead. exact Heq.
    + apply IHtail. exact Heq.
  - intros FDs DI tc_s G S0 C A N A' N' dc binds body tc fieldtcs tc_res l r
      Hdc Htc Hfields Hstore Hbody IHbody G' Heq.
    eapply T_Pat; eauto.
    apply IHbody. apply tenv_equiv_extend_list. exact Heq.
  - intros FDs DI tc_s G S0 C A N t G' Heq.
    constructor.
  - intros FDs DI tc_s G S0 C A N A1 N1 A2 N2 t p ps Hpat IHpat Hps IHps G' Heq.
    eapply T_PatsCons.
    + apply IHpat. exact Heq.
    + apply IHps. exact Heq.
Qed.

Corollary expr_has_type_tenv_equiv :
  forall FDs DI G Sigma C A N A' N' e T,
    has_type FDs DI G Sigma C A N A' N' e T ->
    forall G', tenv_equiv G G' ->
    has_type FDs DI G' Sigma C A N A' N' e T.
Proof.
  intros. destruct has_type_tenv_equiv as [Hexpr _]. eauto.
Qed.

Corollary pat_has_type_tenv_equiv :
  forall FDs DI tc_s G Sigma C A N A' N' T p,
    pat_has_type FDs DI tc_s G Sigma C A N A' N' T p ->
    forall G', tenv_equiv G G' ->
    pat_has_type FDs DI tc_s G' Sigma C A N A' N' T p.
Proof.
  intros. destruct has_type_tenv_equiv as [_ [Hpat _]].
  eauto.
Qed.

Corollary pats_have_type_tenv_equiv :
  forall FDs DI tc_s G Sigma C A N A' N' T ps,
    pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps ->
    forall G', tenv_equiv G G' ->
    pats_have_type FDs DI tc_s G' Sigma C A N A' N' T ps.
Proof.
  intros. destruct has_type_tenv_equiv as [_ [_ Hps]].
  eauto.
Qed.

Lemma store_extends_extend_store :
  forall Sigma Sigma' lr tc,
    store_extends Sigma Sigma' ->
    store_extends (extend_store Sigma lr tc) (extend_store Sigma' lr tc).
Proof.
  intros Sigma Sigma' lr tc Hext lr' tc' Hin.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - left. exact Heq.
  - right. apply Hext. exact Hin.
Qed.

Lemma store_extends_extend_store_list :
  forall Sigma Sigma' entries,
    store_extends Sigma Sigma' ->
    store_extends (extend_store_list Sigma entries)
                  (extend_store_list Sigma' entries).
Proof.
  intros Sigma Sigma' entries.
  revert Sigma Sigma'.
  induction entries as [| ent entries IH]; intros Sigma Sigma' Hext; simpl.
  - exact Hext.
  - destruct ent as [lr0 tc0].
    apply IH. apply store_extends_extend_store. exact Hext.
Qed.

Lemma conloc_extends_extend_conloc :
  forall C C' lr le,
    conloc_extends C C' ->
    conloc_extends (extend_conloc C lr le) (extend_conloc C' lr le).
Proof.
  intros C C' lr le Hext lr' le' Hin.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - left. exact Heq.
  - right. apply Hext. exact Hin.
Qed.

Lemma constructor_layout_extends :
  forall C C' root_l r prev_tc fields,
    constructor_layout C root_l r prev_tc fields ->
    conloc_extends C C' ->
    constructor_layout C' root_l r prev_tc fields.
Proof.
  intros C C' root_l r prev_tc fields Hlayout Hext.
  revert root_l prev_tc Hlayout.
  induction fields as [| [lf tc] fields IH]; intros root_l prev_tc Hlayout; simpl in *.
  - exact I.
  - destruct Hlayout as [Hhd Htl]. split.
    + destruct prev_tc.
      * apply Hext. exact Hhd.
      * apply Hext. exact Hhd.
    + apply IH; assumption.
Qed.

Lemma store_wf_extend_store_existing :
  forall DI Sigma C A N M S lr tc,
    store_wf DI Sigma C A N M S ->
    In (lr, tc) Sigma ->
    store_wf DI (extend_store Sigma lr tc) C A N M S.
Proof.
  intros DI Sigma C A N M S lr tc Hwf Hin_old.
  destruct Hwf as [Hmap [Hcfc [Halloc [Hdisj1 Hdisj2]]]].
  destruct Hcfc as [Hstart [Hnext Hafter]].
  destruct Halloc as [Hlin1 [Hlin2 [Hwrite [Hempty Htracked]]]].
  repeat split.
  - intros l r T Hin.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. eapply Hmap. exact Hin_old.
    + eapply Hmap. exact Hin.
  - exact Hstart.
  - exact Hnext.
  - exact Hafter.
  - exact Hlin1.
  - exact Hlin2.
  - exact Hwrite.
  - exact Hempty.
  - exact Htracked.
  - intros l r T Hin.
    simpl in Hin. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. eapply Hdisj1. exact Hin_old.
    + eapply Hdisj1. exact Hin.
  - intros l r HinN Hex.
    simpl in Hex. destruct Hex as [T [Heq | Hin]].
    + inversion Heq; subst. eapply Hdisj2; eauto.
    + eapply Hdisj2; eauto.
Qed.

Lemma store_wf_extend_alloc_none_fresh :
  forall DI Sigma C A N M S r,
    store_wf DI Sigma C A N M S ->
    fresh_region A r ->
    store_wf DI Sigma C (extend_alloc A r AP_None) N M S.
Proof.
  intros DI Sigma C A N M S r Hwf Hfresh.
  destruct Hwf as [Hmap [Hcfc [Halloc [Hdisj1 Hdisj2]]]].
  destruct Hcfc as [Hstart [Hnext Hafter]].
  destruct Halloc as [Hlin1 [Hlin2 [Hwrite [Hempty Htracked]]]].
  assert (Hallocwf : alloc_wf DI A N M S).
  { repeat split; assumption. }
  repeat split.
  - exact Hmap.
  - exact Hstart.
  - exact Hnext.
  - exact Hafter.
  - intros r' l HinA HinN.
    destruct HinA as [Heq | HinA].
    + inversion Heq.
    + apply filter_In in HinA as [HinA _].
      eapply Hlin1; eauto.
  - intros r' l i T j HinA Hlk Hnin Hew.
    destruct HinA as [Heq | HinA].
    + inversion Heq.
    + apply filter_In in HinA as [HinA _].
      eapply Hlin2; eauto.
  - exact Hwrite.
  - intros r' HinA.
    destruct HinA as [Heq | HinA].
    + inversion Heq; subst.
      exact (fresh_region_store_absent _ _ _ _ _ _ Hallocwf Hfresh).
    + apply filter_In in HinA as [HinA _].
      eapply Hempty; eauto.
  - intros r' Hheap.
    destruct (region_var_eq_dec r' r) as [Heq | Hneq].
    + subst. exfalso.
      rewrite (fresh_region_store_absent _ _ _ _ _ _ Hallocwf Hfresh) in Hheap.
      contradiction.
    + destruct (Htracked r' Hheap) as [l Hin].
      exists l. eapply in_extend_alloc_old; eauto.
  - exact Hdisj1.
  - exact Hdisj2.
Qed.

Lemma store_wf_extend_letloc_start :
  forall DI Sigma C A N M S l r,
    store_wf DI Sigma C A N M S ->
    letloc_fresh_ctx Sigma C A N (l, r) ->
    In (r, AP_None) A ->
    store_wf DI Sigma
             (extend_conloc C (l, r) (LE_Start r))
             (extend_alloc A r (AP_Loc (l, r)))
             (extend_nursery N (l, r))
             (extend_loc M (l, r) (r, 0))
             S.
Proof.
  intros DI Sigma C A N M S l r Hwf Hfresh Hnone.
  destruct Hfresh as [HfreshS [HfreshC [HfreshA HfreshN]]].
  destruct Hwf as [Hmap [Hcfc [Halloc [Hdisj1 Hdisj2]]]].
  destruct Hcfc as [Hstart [Hnext Hafter]].
  destruct Halloc as [Hlin1 [Hlin2 [Hwrite [Hempty Htracked]]]].
  repeat split.
  - intros l0 r0 T HinSigma.
    destruct (Hmap l0 r0 T HinSigma) as [i [j [Hlk Hew]]].
    exists i, j. split.
    + rewrite lookup_loc_extend_neq.
      * exact Hlk.
      * intro Heq. apply HfreshS. rewrite <- Heq.
        eapply in_store_laddrs_of_entry. exact HinSigma.
    + exact Hew.
  - intros l0 r0 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq; subst. apply lookup_loc_extend_eq.
    + rewrite lookup_loc_extend_neq.
      * eapply Hstart. exact HinC.
      * intro Heq. apply HfreshC. rewrite <- Heq.
        eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 lprev HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + destruct (Hnext l0 r0 lprev HinC) as [i [Hsrc Hdst]].
      exists i. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs with (lr' := (l0, r0)) (le := LE_Next lprev r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 T l1 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + destruct (Hafter l0 r0 T l1 HinC) as [i [j [Hsrc [Hew Hdst]]]].
      exists i, j. repeat split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs with (lr' := (l0, r0)) (le := LE_After T l1 r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * exact Hew.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros r0 l0 HinA HinN.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exists 0. split.
      * apply lookup_loc_extend_eq.
      * unfold gt_allocptr, allocptr.
        rewrite (Hempty _ Hnone). reflexivity.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshA. rewrite <- Heq.
        eapply in_alloc_laddrs_of_entry. exact HinA_old. }
      destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [HeqN | HinN_old].
      * contradiction.
      * destruct (Hlin1 r0 l0 HinA_old HinN_old) as [i [Hlk Hgt]].
        exists i. split.
        -- rewrite lookup_loc_extend_neq.
           ++ exact Hlk.
           ++ exact Hneq_lr.
        -- exact Hgt.
  - intros r0 l0 i T j HinA Hlk Hnin Hew.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exfalso. apply Hnin. simpl. left. reflexivity.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshA. rewrite <- Heq.
        eapply in_alloc_laddrs_of_entry. exact HinA_old. }
      destruct (not_in_extend_nursery_inv N (l, r) (l0, r0) Hnin) as [_ Hnin_old].
      rewrite lookup_loc_extend_neq in Hlk by exact Hneq_lr.
      eapply Hlin2; eauto.
  - intros l0 r0 HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + inversion Heq; subst. exists 0. split.
      * apply lookup_loc_extend_eq.
      * unfold heap_lookup. rewrite (Hempty _ Hnone). reflexivity.
    + assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshN. rewrite Heq in HinN_old. exact HinN_old. }
      destruct (Hwrite l0 r0 HinN_old) as [i [Hlk Hnone_cell]].
      exists i. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hlk.
        -- exact Hneq_lr.
      * exact Hnone_cell.
  - intros r0 HinA.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      eapply Hempty. exact HinA_old.
  - intros r0 Hheap.
    destruct (region_var_eq_dec r0 r) as [Heq | Hneq].
    + subst. exists l. apply in_extend_alloc_new.
    + destruct (Htracked r0 Hheap) as [l0 HinA].
      exists l0. eapply in_extend_alloc_old; eauto.
  - intros l0 r0 T HinSigma HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj1; eauto.
  - intros l0 r0 HinN HexSigma.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + destruct HexSigma as [T HinSigma].
      apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj2; eauto.
Qed.

Lemma store_wf_extend_letloc_tag :
  forall DI Sigma C A N M S l lprev r i,
    store_wf DI Sigma C A N M S ->
    letloc_fresh_ctx Sigma C A N (l, r) ->
    In (r, AP_Loc (lprev, r)) A ->
    In (lprev, r) N ->
    lookup_loc M (lprev, r) = Some (r, i) ->
    store_wf DI Sigma
             (extend_conloc C (l, r) (LE_Next lprev r))
             (extend_alloc A r (AP_Loc (l, r)))
             (extend_nursery N (l, r))
             (extend_loc M (l, r) (r, i + 1))
             S.
Proof.
  intros DI Sigma C A N M S l lprev r i Hwf Hfresh Hfocus_prev Hnur_prev Hlookup_prev.
  destruct Hfresh as [HfreshS [HfreshC [HfreshA HfreshN]]].
  destruct Hwf as [Hmap [Hcfc [Halloc [Hdisj1 Hdisj2]]]].
  destruct Hcfc as [Hstart [Hnext Hafter]].
  destruct Halloc as [Hlin1 [Hlin2 [Hwrite [Hempty Htracked]]]].
  assert (Hgt_prev : gt_allocptr i (allocptr S r)).
  { destruct (Hlin1 r lprev Hfocus_prev Hnur_prev) as [i0 [Hlk0 Hgt0]].
    rewrite Hlookup_prev in Hlk0. inversion Hlk0; subst. exact Hgt0. }
  repeat split.
  - intros l0 r0 T HinSigma.
    destruct (Hmap l0 r0 T HinSigma) as [i0 [j [Hlk Hew]]].
    exists i0, j. split.
    + rewrite lookup_loc_extend_neq.
      * exact Hlk.
      * intro Heq. apply HfreshS. rewrite <- Heq.
        eapply in_store_laddrs_of_entry. exact HinSigma.
    + exact Hew.
  - intros l0 r0 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + rewrite lookup_loc_extend_neq.
      * eapply Hstart. exact HinC.
      * intro Heq. apply HfreshC. rewrite <- Heq.
        eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 lprev0 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq; subst. exists i. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hlookup_prev.
        -- intro Heq_lr. apply HfreshA. rewrite <- Heq_lr.
           eapply in_alloc_laddrs_of_entry. exact Hfocus_prev.
      * apply lookup_loc_extend_eq.
    + destruct (Hnext l0 r0 lprev0 HinC) as [i0 [Hsrc Hdst]].
      exists i0. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs
             with (lr' := (l0, r0)) (le := LE_Next lprev0 r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 T l1 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + destruct (Hafter l0 r0 T l1 HinC) as [i0 [j [Hsrc [Hew Hdst]]]].
      exists i0, j. repeat split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs
             with (lr' := (l0, r0)) (le := LE_After T l1 r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * exact Hew.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros r0 l0 HinA HinN.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exists (i + 1). split.
      * apply lookup_loc_extend_eq.
      * apply gt_allocptr_succ. exact Hgt_prev.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old Hrneq].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. inversion Heq; subst. contradiction. }
      destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [HeqN | HinN_old].
      * inversion HeqN; subst. contradiction.
      * destruct (Hlin1 r0 l0 HinA_old HinN_old) as [i0 [Hlk Hgt]].
        exists i0. split.
        -- rewrite lookup_loc_extend_neq.
           ++ exact Hlk.
           ++ exact Hneq_lr.
        -- exact Hgt.
  - intros r0 l0 i0 T j HinA Hlk Hnin Hew.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exfalso. apply Hnin. simpl. left. reflexivity.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshA. rewrite <- Heq.
        eapply in_alloc_laddrs_of_entry. exact HinA_old. }
      destruct (not_in_extend_nursery_inv N (l, r) (l0, r0) Hnin) as [_ Hnin_old].
      rewrite lookup_loc_extend_neq in Hlk by exact Hneq_lr.
      eapply Hlin2; eauto.
  - intros l0 r0 HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + inversion Heq; subst. exists (i + 1). split.
      * apply lookup_loc_extend_eq.
      * eapply gt_allocptr_heap_lookup_none.
        apply gt_allocptr_succ. exact Hgt_prev.
    + assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshN. rewrite Heq in HinN_old. exact HinN_old. }
      destruct (Hwrite l0 r0 HinN_old) as [i0 [Hlk Hnone_cell]].
      exists i0. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hlk.
        -- exact Hneq_lr.
      * exact Hnone_cell.
  - intros r0 HinA.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      eapply Hempty. exact HinA_old.
  - intros r0 Hheap.
    destruct (region_var_eq_dec r0 r) as [Heq | Hneq].
    + subst. exists l. apply in_extend_alloc_new.
    + destruct (Htracked r0 Hheap) as [l0 HinA].
      exists l0. eapply in_extend_alloc_old; eauto.
  - intros l0 r0 T HinSigma HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj1; eauto.
  - intros l0 r0 HinN HexSigma.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + destruct HexSigma as [T HinSigma].
      apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj2; eauto.
Qed.

Lemma store_wf_extend_letloc_after :
  forall DI Sigma C A N M S l l1 r tc_prev i j,
    store_wf DI Sigma C A N M S ->
    letloc_fresh_ctx Sigma C A N (l, r) ->
    In (r, AP_Loc (l1, r)) A ->
    In ((l1, r), tc_prev) Sigma ->
    ~ In (l1, r) N ->
    lookup_loc M (l1, r) = Some (r, i) ->
    end_witness DI S (r, i) tc_prev (r, j) ->
    store_wf DI Sigma
             (extend_conloc C (l, r) (LE_After tc_prev l1 r))
             (extend_alloc A r (AP_Loc (l, r)))
             (extend_nursery N (l, r))
             (extend_loc M (l, r) (r, j))
             S.
Proof.
  intros DI Sigma C A N M S l l1 r tc_prev i j
         Hwf Hfresh Hfocus_prev Hstore_prev Hnotin_prev Hlookup_prev Hew_prev.
  destruct Hfresh as [HfreshS [HfreshC [HfreshA HfreshN]]].
  destruct Hwf as [Hmap [Hcfc [Halloc [Hdisj1 Hdisj2]]]].
  destruct Hcfc as [Hstart [Hnext Hafter]].
  destruct Halloc as [Hlin1 [Hlin2 [Hwrite [Hempty Htracked]]]].
  assert (Hgt_prev : gt_allocptr j (allocptr S r)).
  { eapply Hlin2; eauto. }
  repeat split.
  - intros l0 r0 T HinSigma.
    destruct (Hmap l0 r0 T HinSigma) as [i0 [j0 [Hlk Hew]]].
    exists i0, j0. split.
    + rewrite lookup_loc_extend_neq.
      * exact Hlk.
      * intro Heq. apply HfreshS. rewrite <- Heq.
        eapply in_store_laddrs_of_entry. exact HinSigma.
    + exact Hew.
  - intros l0 r0 HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + rewrite lookup_loc_extend_neq.
      * eapply Hstart. exact HinC.
      * intro Heq. apply HfreshC. rewrite <- Heq.
        eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 lprev HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq.
    + destruct (Hnext l0 r0 lprev HinC) as [i0 [Hsrc Hdst]].
      exists i0. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs
             with (lr' := (l0, r0)) (le := LE_Next lprev r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros l0 r0 T l0' HinC.
    simpl in HinC. destruct HinC as [Heq | HinC].
    + inversion Heq; subst. exists i, j. repeat split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hlookup_prev.
        -- intro Heq_lr. apply HfreshA. rewrite <- Heq_lr.
           eapply in_alloc_laddrs_of_entry. exact Hfocus_prev.
      * exact Hew_prev.
      * apply lookup_loc_extend_eq.
    + destruct (Hafter l0 r0 T l0' HinC) as [i0 [j0 [Hsrc [Hew Hdst]]]].
      exists i0, j0. repeat split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hsrc.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_rhs
             with (lr' := (l0, r0)) (le := LE_After T l0' r0).
           ++ exact HinC.
           ++ simpl. left. reflexivity.
      * exact Hew.
      * rewrite lookup_loc_extend_neq.
        -- exact Hdst.
        -- intro Heq. apply HfreshC. rewrite <- Heq.
           eapply in_conloc_support_of_key. exact HinC.
  - intros r0 l0 HinA HinN.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exists j. split.
      * apply lookup_loc_extend_eq.
      * exact Hgt_prev.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old Hrneq].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. inversion Heq; subst. contradiction. }
      destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [HeqN | HinN_old].
      * inversion HeqN; subst. contradiction.
      * destruct (Hlin1 r0 l0 HinA_old HinN_old) as [i0 [Hlk Hgt]].
        exists i0. split.
        -- rewrite lookup_loc_extend_neq.
           ++ exact Hlk.
           ++ exact Hneq_lr.
        -- exact Hgt.
  - intros r0 l0 i0 T j0 HinA Hlk Hnin Hew.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq; subst. exfalso. apply Hnin. simpl. left. reflexivity.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshA. rewrite <- Heq.
        eapply in_alloc_laddrs_of_entry. exact HinA_old. }
      destruct (not_in_extend_nursery_inv N (l, r) (l0, r0) Hnin) as [_ Hnin_old].
      rewrite lookup_loc_extend_neq in Hlk by exact Hneq_lr.
      eapply Hlin2; eauto.
  - intros l0 r0 HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + inversion Heq; subst. exists j. split.
      * apply lookup_loc_extend_eq.
      * eapply gt_allocptr_heap_lookup_none. exact Hgt_prev.
    + assert (Hneq_lr : (l0, r0) <> (l, r)).
      { intro Heq. apply HfreshN. rewrite Heq in HinN_old. exact HinN_old. }
      destruct (Hwrite l0 r0 HinN_old) as [i0 [Hlk Hnone_cell]].
      exists i0. split.
      * rewrite lookup_loc_extend_neq.
        -- exact Hlk.
        -- exact Hneq_lr.
      * exact Hnone_cell.
  - intros r0 HinA.
    simpl in HinA. destruct HinA as [Heq | HinA].
    + inversion Heq.
    + destruct (in_remove_alloc_region_inv _ _ _ _ HinA) as [HinA_old _].
      eapply Hempty. exact HinA_old.
  - intros r0 Hheap.
    destruct (region_var_eq_dec r0 r) as [Heq | Hneq].
    + subst. exists l. apply in_extend_alloc_new.
    + destruct (Htracked r0 Hheap) as [l0 HinA].
      exists l0. eapply in_extend_alloc_old; eauto.
  - intros l0 r0 T HinSigma HinN.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj1; eauto.
  - intros l0 r0 HinN HexSigma.
    destruct (in_extend_nursery_inv N (l, r) (l0, r0) HinN) as [Heq | HinN_old].
    + destruct HexSigma as [T HinSigma].
      apply HfreshS. rewrite <- Heq. eapply in_store_laddrs_of_entry. exact HinSigma.
    + eapply Hdisj2; eauto.
Qed.

Lemma has_type_sigma_c_monotone :
  (forall FDs DI G Sigma C A N A' N' e T,
      has_type FDs DI G Sigma C A N A' N' e T ->
      forall Sigma' C',
        store_extends Sigma Sigma' ->
        conloc_extends C C' ->
        has_type FDs DI G Sigma' C' A N A' N' e T)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T p,
      pat_has_type FDs DI tc_s G Sigma C A N A' N' T p ->
      forall Sigma' C',
        store_extends Sigma Sigma' ->
        conloc_extends C C' ->
        pat_has_type FDs DI tc_s G Sigma' C' A N A' N' T p)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T ps,
      pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps ->
      forall Sigma' C',
        store_extends Sigma Sigma' ->
        conloc_extends C C' ->
        pats_have_type FDs DI tc_s G Sigma' C' A N A' N' T ps).
Proof.
  eapply typing_mutind
    with
      (P0 := fun FDs DI G Sigma C A N r vs fields HT =>
               forall Sigma' C',
                 store_extends Sigma Sigma' ->
                 conloc_extends C C' ->
                 field_vals_have_type FDs DI G Sigma' C' A N r vs fields)
      (P1 := fun FDs DI G Sigma C A N formals actuals vs params HT =>
               forall Sigma' C',
                 store_extends Sigma Sigma' ->
                 conloc_extends C C' ->
                 app_vals_have_type FDs DI G Sigma' C' A N formals actuals vs params).
  - intros FDs DI G S0 C A N x tc l r Hlookup Hstore Sigma' C' Hse Hce.
    apply T_Var.
    + exact Hlookup.
    + apply Hse. exact Hstore.
  - intros FDs DI G S0 C A N r0 i l r tc Hstore Sigma' C' Hse Hce.
    apply T_ConcreteLoc. apply Hse. exact Hstore.
  - intros FDs DI G S0 C A N A' N' A'' N'' x e1 e2 tc1 l1 r1 tc2 l2 r2
      Hty1 IH1 Hty2 IH2 Sigma' C' Hse Hce.
    eapply T_Let.
    + apply IH1; assumption.
    + apply IH2.
      * apply store_extends_extend_store. exact Hse.
      * exact Hce.
  - intros FDs DI G S0 C A N A' N' r e t Hfresh Hty IH Sigma' C' Hse Hce.
    eapply T_LRegion.
    + exact Hfresh.
    + apply IH; assumption.
  - intros FDs DI G S0 C A N A'' N'' l r e tc' l' r'
      Halloc HfreshOut Hneq
      Hty IH Sigma' C' Hse Hce.
    eapply T_LLStart; eauto.
    apply IH.
    + exact Hse.
    + apply conloc_extends_extend_conloc. exact Hce.
  - intros FDs DI G S0 C A N A'' N'' l lprev r e tc'' l'' r''
      Halloc Hnur HfreshOut Hneq Hty IH Sigma' C' Hse Hce.
    eapply T_LLTag; eauto.
    apply IH.
    + exact Hse.
    + apply conloc_extends_extend_conloc. exact Hce.
  - intros FDs DI G S0 C A N A'' N'' l l1 r tc_prev e tc' l' r'
      Halloc Hstore Hnotin HfreshOut Hneq
      Hty IH Sigma' C' Hse Hce.
    eapply T_LLAfter.
    + exact Halloc.
    + apply Hse. exact Hstore.
    + exact Hnotin.
    + exact HfreshOut.
    + exact Hneq.
    + apply IH.
      * exact Hse.
      * apply conloc_extends_extend_conloc. exact Hce.
  - intros FDs DI G S0 C A N dc l r vs tc fieldtcs fields
      Hdc Hnur Hfields Hlayout Hfocus Hvals IHvals Sigma' C' Hse Hce.
    eapply T_DataCon.
    + exact Hdc.
    + exact Hnur.
    + exact Hfields.
    + apply constructor_layout_extends with (C := C); assumption.
    + exact Hfocus.
    + apply IHvals; assumption.
  - intros FDs DI G S0 C A N f lrs vs tc l r f_locs f_params f_retty
      f_regions f_body Hfd Hnur Halloc Hlen Hret Hargs IHargs Sigma' C' Hse Hce.
    eapply T_App.
    + exact Hfd.
    + exact Hnur.
    + exact Halloc.
    + exact Hlen.
    + exact Hret.
    + apply IHargs; assumption.
  - intros FDs DI G S0 C A N A' N' scrut ps tc_s l_s r_s t
      Hscrut IHscrut Hcover Hps IHps Sigma' C' Hse Hce.
    eapply T_Case.
    + apply IHscrut; assumption.
    + exact Hcover.
    + apply IHps; assumption.
  - intros FDs DI G S0 C A N r Sigma' C' Hse Hce.
    apply T_FieldValsNil.
  - intros FDs DI G S0 C A N r vl fld vs flds Hhead IHhead Htail IHtail
      Sigma' C' Hse Hce.
    eapply T_FieldValsCons.
    + apply IHhead; assumption.
    + apply IHtail; assumption.
  - intros FDs DI G S0 C A N formals actuals Sigma' C' Hse Hce.
    apply T_AppValsNil.
  - intros FDs DI G S0 C A N formals actuals vl param vs params
      Hhead IHhead Htail IHtail Sigma' C' Hse Hce.
    eapply T_AppValsCons.
    + apply IHhead; assumption.
    + apply IHtail; assumption.
  - intros FDs DI tc_s G S0 C A N A' N' dc binds body tc fieldtcs tc_res l r
      Hdc Htc Hfields Hstore Hbody IHbody Sigma' C' Hse Hce.
    eapply T_Pat.
    + exact Hdc.
    + exact Htc.
    + exact Hfields.
    + apply Hse. exact Hstore.
    + eapply (IHbody (extend_store_list Sigma' (pat_store_entries binds)) C').
      * apply store_extends_extend_store_list. exact Hse.
      * exact Hce.
  - intros FDs DI tc_s G S0 C A N t Sigma' C' Hse Hce.
    apply T_PatsNil.
  - intros FDs DI tc_s G S0 C A N A1 N1 A2 N2 t p ps Hpat IHpat Hps IHps
      Sigma' C' Hse Hce.
    eapply T_PatsCons.
    + apply IHpat; assumption.
    + apply IHps; assumption.
Qed.

Corollary expr_has_type_sigma_c_monotone :
  forall FDs DI G Sigma C A N A' N' e T,
    has_type FDs DI G Sigma C A N A' N' e T ->
    forall Sigma' C',
      store_extends Sigma Sigma' ->
      conloc_extends C C' ->
      has_type FDs DI G Sigma' C' A N A' N' e T.
Proof.
  intros. destruct has_type_sigma_c_monotone as [Hex _]. eauto.
Qed.

Corollary pat_has_type_sigma_c_monotone :
  forall FDs DI tc_s G Sigma C A N A' N' T p,
    pat_has_type FDs DI tc_s G Sigma C A N A' N' T p ->
    forall Sigma' C',
      store_extends Sigma Sigma' ->
      conloc_extends C C' ->
      pat_has_type FDs DI tc_s G Sigma' C' A N A' N' T p.
Proof.
  intros. destruct has_type_sigma_c_monotone as [_ [Hpat _]]. eauto.
Qed.

Corollary pats_have_type_sigma_c_monotone :
  forall FDs DI tc_s G Sigma C A N A' N' T ps,
    pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps ->
    forall Sigma' C',
      store_extends Sigma Sigma' ->
      conloc_extends C C' ->
      pats_have_type FDs DI tc_s G Sigma' C' A N A' N' T ps.
Proof.
  intros. destruct has_type_sigma_c_monotone as [_ [_ Hps]]. eauto.
Qed.

Lemma existsb_bind_hit :
  forall x (binds : list (term_var * ty)),
    existsb
      (fun b => if term_var_eq_dec x (fst b) then true else false)
      binds = true ->
    exists t : ty, In (x, t) binds.
Proof.
  intros x0 binds. induction binds as [| [y t] binds IH]; intros Hhit; simpl in *.
  - discriminate.
  - destruct (term_var_eq_dec x0 y).
    + exists t. left. subst. reflexivity.
    + apply IH in Hhit as [t' Hin]. exists t'. right. exact Hin.
Qed.

Lemma existsb_bind_miss :
  forall x (binds : list (term_var * ty)) t,
    existsb
      (fun b => if term_var_eq_dec x (fst b) then true else false)
      binds = false ->
    ~ In (x, t) binds.
Proof.
  intros x0 binds. induction binds as [| [y u] binds IH]; intros t Hmiss Hin; simpl in *.
  - exact Hin.
  - destruct (term_var_eq_dec x0 y) as [Heq | Hneq].
    + discriminate.
    + destruct Hin as [Hin | Hin].
      * inversion Hin; subst. contradiction.
      * eapply IH; eauto.
Qed.

Lemma in_extend_store_list :
  forall S0 entries ent,
    In ent S0 ->
    In ent (extend_store_list S0 entries).
Proof.
  intros S0 entries ent Hin. revert S0 ent Hin.
  induction entries as [| entry entries IH]; intros S0 ent Hin; simpl.
  - exact Hin.
  - apply IH. simpl. right. exact Hin.
Qed.

Lemma lookup_tenv_extend_tenv_list_miss :
  forall G binds x,
    lookup_tenv G x = None ->
    existsb
      (fun b => if term_var_eq_dec x (fst b) then true else false)
      binds = false ->
    lookup_tenv (extend_tenv_list G binds) x = None.
Proof.
  intros G binds. revert G.
  induction binds as [| [y t] binds IH]; intros G x Hlookup Hmiss; simpl in *.
  - exact Hlookup.
  - destruct (term_var_eq_dec x y) as [Heq | Hneq].
    + discriminate.
    + apply IH.
      * simpl. destruct (term_var_eq_dec x y); [contradiction | exact Hlookup].
      * exact Hmiss.
Qed.

Lemma tenv_equiv_shadow_under_binds_prefix :
  forall prefix Gamma binds x t,
    existsb
      (fun b => if term_var_eq_dec x (fst b) then true else false)
      binds = true ->
    tenv_equiv (extend_tenv_list ((prefix ++ (x, t) :: Gamma)%list) binds)
               (extend_tenv_list ((prefix ++ Gamma)%list) binds).
Proof.
  intros prefix Gamma binds x t Hhit.
  rewrite !(extend_tenv_list_app prefix).
  eapply (tenv_equiv_shadow_under_prefix ((rev binds ++ prefix)%list) Gamma x t).
  apply existsb_bind_hit in Hhit as [t' Hin].
  destruct (in_lookup_tenv (rev binds) x t') as [t'' Hlookup].
  - apply (proj1 (in_rev binds (x, t'))). exact Hin.
  - intro Hnone.
    rewrite lookup_tenv_app in Hnone.
    rewrite Hlookup in Hnone.
    discriminate.
Qed.

Lemma in_subst_pats_val :
  forall dc binds body ps z s,
    In (pat_clause dc binds body) ps ->
    exists body',
      In (pat_clause dc binds body') (subst_pats_val z s ps).
Proof.
  intros dc binds body ps z s Hin.
  induction ps as [| [dc' binds' body''] ps IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst.
      exists
        (if existsb
              (fun b => if term_var_eq_dec z (fst b) then true else false)
              binds
         then body
         else subst_val z s body).
      left.
      destruct
        (existsb
           (fun b => if term_var_eq_dec z (fst b) then true else false)
           binds); reflexivity.
    + destruct (IH Hin) as [body' Hin'].
      exists body'. right. exact Hin'.
Qed.

Lemma pats_cover_subst_pats_val :
  forall DI tc ps z s,
    pats_cover DI tc ps ->
    pats_cover DI tc (subst_pats_val z s ps).
Proof.
  intros DI tc ps z s Hcover K fts Hin.
  destruct (Hcover K fts Hin) as [binds [body Hinps]].
  destruct (in_subst_pats_val K binds body ps z s Hinps) as [body' Hin'].
  exists binds, body'. exact Hin'.
Qed.

Lemma subst_case_pats_eq :
  forall z s ps,
    (let fix go_pats (ps : list pat) : list pat :=
       match ps with
       | nil => nil
       | pat_clause K binds body :: ps' =>
           (if existsb
                 (fun b => if term_var_eq_dec z (fst b) then true else false)
                 binds
            then pat_clause K binds body
            else pat_clause K binds (subst_val z s body))
           :: go_pats ps'
       end
     in go_pats ps) = subst_pats_val z s ps.
Proof.
  intros z s ps.
  induction ps as [| [K binds body] ps IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma subst_val_case :
  forall z s scrut ps,
    subst_val z s (e_case scrut ps) =
    e_case (subst_in_val z s scrut) (subst_pats_val z s ps).
Proof.
  intros z s scrut ps.
  simpl. f_equal.
  induction ps as [| [K binds body] ps IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* ================================================================= *)
(* Lemma: Substitution  (thesis Appendix A, Lemma Substitution)       *)
(*                                                                    *)
(* Substituting well-typed values for variables in a well-typed       *)
(* expression preserves typing. For the named-syntax mechanization,   *)
(* open values require an explicit no-capture side condition.         *)
(* The full thesis lemma is more general still: it is simultaneous    *)
(* over value, location, and region substitution under the thesis's   *)
(* global uniquify convention.                                        *)
(* ================================================================= *)

Fixpoint pats_bound_term_vars (ps : list pat) : list term_var :=
  match ps with
  | nil => nil
  | p :: ps' => pat_bound_term_vars p ++ pats_bound_term_vars ps'
  end.

Lemma value_typing_extend_tenv_miss :
  forall FDs DI G Sigma C A N vl T x tx,
    has_type FDs DI G Sigma C A N A N (e_val vl) T ->
    ~ In x (val_term_vars vl) ->
    has_type FDs DI (extend_tenv G x tx) Sigma C A N A N (e_val vl) T.
Proof.
  intros FDs DI G Sigma C A N vl T x tx Hty Hmiss.
  inversion Hty; subst; simpl in *.
  - apply T_Var.
    + simpl. destruct (term_var_eq_dec x0 x) as [Heq | Hneq].
      * subst. exfalso. apply Hmiss. simpl. left. reflexivity.
      * match goal with
        | [ Hlk : lookup_tenv G x0 = Some _ |- _ ] => exact Hlk
        end.
    + match goal with
      | [ Hstore : In ((l, r), tc) Sigma |- _ ] => exact Hstore
      end.
  - apply T_ConcreteLoc.
    match goal with
    | [ Hstore : In ((l, r), tc) Sigma |- _ ] => exact Hstore
    end.
Qed.

Lemma value_typing_extend_tenv_list_disjoint :
  forall FDs DI G Sigma C A N vl T binds,
    has_type FDs DI G Sigma C A N A N (e_val vl) T ->
    (forall x t, In (x, t) binds -> ~ In x (val_term_vars vl)) ->
    has_type FDs DI (extend_tenv_list G binds) Sigma C A N A N (e_val vl) T.
Proof.
  intros FDs DI G Sigma C A N vl T binds Hty.
  revert G Hty.
  induction binds as [| [x t] binds IH]; intros G Hty Hdisj; simpl.
  - exact Hty.
  - apply IH.
    + eapply value_typing_extend_tenv_miss.
      * exact Hty.
      * eapply Hdisj. left. reflexivity.
    + intros y ty Hin.
      eapply Hdisj. right. exact Hin.
Qed.

Definition subst_expr_case
    FDs DI G Sigma C A N A' N' e T
    (HT : has_type FDs DI G Sigma C A N A' N' e T) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A N (e_val s) uty ->
    (forall y, In y (val_term_vars s) -> ~ In y (expr_bound_term_vars e)) ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A' N' (subst_val z s e) T.

Definition subst_pat_case
    FDs DI tc_s G Sigma C A N A' N' T p
    (HT : pat_has_type FDs DI tc_s G Sigma C A N A' N' T p) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A N (e_val s) uty ->
    (forall y, In y (val_term_vars s) -> ~ In y (pat_bound_term_vars p)) ->
    pat_has_type FDs DI tc_s (prefix ++ Gamma)%list Sigma C A N A' N' T (subst_pat_val z s p).

Definition subst_field_vals_case
    FDs DI G Sigma C A N r vs fields
    (HT : field_vals_have_type FDs DI G Sigma C A N r vs fields) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A N (e_val s) uty ->
    field_vals_have_type FDs DI (prefix ++ Gamma)%list Sigma C A N r
      (List.map (subst_in_val z s) vs) fields.

Definition subst_app_vals_case
    FDs DI G Sigma C A N formals actuals vs params
    (HT : app_vals_have_type FDs DI G Sigma C A N formals actuals vs params) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A N (e_val s) uty ->
    app_vals_have_type FDs DI (prefix ++ Gamma)%list Sigma C A N formals actuals
      (List.map (subst_in_val z s) vs) params.

Definition subst_pats_case
    FDs DI tc_s G Sigma C A N A' N' T ps
    (HT : pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A N (e_val s) uty ->
    (forall y, In y (val_term_vars s) -> ~ In y (pats_bound_term_vars ps)) ->
    pats_have_type FDs DI tc_s (prefix ++ Gamma)%list Sigma C A N A' N' T (subst_pats_val z s ps).

Lemma substitution_val_mutual :
  (forall FDs DI G Sigma C A N A' N' e T
      (HT : has_type FDs DI G Sigma C A N A' N' e T),
      subst_expr_case FDs DI G Sigma C A N A' N' e T HT)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T p
      (HT : pat_has_type FDs DI tc_s G Sigma C A N A' N' T p),
      subst_pat_case FDs DI tc_s G Sigma C A N A' N' T p HT)
  /\
  (forall FDs DI tc_s G Sigma C A N A' N' T ps
      (HT : pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps),
      subst_pats_case FDs DI tc_s G Sigma C A N A' N' T ps HT).
Proof.
  eapply typing_mutind
    with
      (P0 := fun FDs DI G Sigma C A N r vs fields HT =>
               subst_field_vals_case FDs DI G Sigma C A N r vs fields HT)
      (P1 := fun FDs DI G Sigma C A N formals actuals vs params HT =>
               subst_app_vals_case FDs DI G Sigma C A N formals actuals vs params HT).
  - intros FDs DI G Sigma C A N x tc l r Hlookup Hstore.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl in *.
    rewrite lookup_tenv_app in Hlookup.
    destruct (lookup_tenv prefix x) eqn:Hprefix.
    + destruct (term_var_eq_dec z x) as [Heq | Hneq].
      * subst x. rewrite Hnone in Hprefix. discriminate.
      * inversion Hlookup; subst. simpl.
        apply T_Var.
        -- rewrite lookup_tenv_app. rewrite Hprefix. reflexivity.
        -- exact Hstore.
    + simpl in Hlookup.
      destruct (term_var_eq_dec x z) as [Heq | Hneq].
      * subst x. inversion Hlookup; subst.
        simpl. destruct (term_var_eq_dec z z); [| contradiction].
        exact Hs.
      * simpl. destruct (term_var_eq_dec z x) as [Heqzx | Hneqzx].
        { exfalso. apply Hneq. symmetry. exact Heqzx. }
        apply T_Var.
        -- rewrite lookup_tenv_app. rewrite Hprefix. simpl.
           destruct (term_var_eq_dec x z); [contradiction | exact Hlookup].
        -- exact Hstore.
  - intros FDs DI G Sigma C A N r0 i l r tc Hstore.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl. apply T_ConcreteLoc. exact Hstore.
  - intros FDs DI G Sigma C A N A' N' A'' N'' x e1 e2 tc1 l1 r1 tc2 l2 r2
      Hty1 IH1 Hty2 IH2.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl.
    assert (Hfresh_e1 :
      forall y, In y (val_term_vars s) -> ~ In y (expr_bound_term_vars e1)).
    { intros y Hy Hin.
      apply (Hfresh y Hy). simpl. apply in_or_app. left. exact Hin. }
    eapply T_Let.
    + eapply IH1; eauto.
    + destruct (term_var_eq_dec z x) as [Heq | Hneq].
      * subst x. simpl.
        eapply expr_has_type_tenv_equiv.
        -- exact Hty2.
        -- change (tenv_equiv
                     ((((z, LocTy tc1 l1 r1) :: prefix) ++ (z, uty) :: Gamma)%list)
                     ((((z, LocTy tc1 l1 r1) :: prefix) ++ Gamma)%list)).
           apply tenv_equiv_shadow_under_prefix.
           simpl. destruct (term_var_eq_dec z z); [discriminate | contradiction].
      * simpl.
        assert (Hs_mid :
          has_type FDs DI (((x, LocTy tc1 l1 r1) :: prefix ++ Gamma)%list)
                   Sigma C A N A N (e_val s) uty).
        { change (((x, LocTy tc1 l1 r1) :: prefix ++ Gamma)%list)
            with (extend_tenv ((prefix ++ Gamma)%list) x (LocTy tc1 l1 r1)).
          eapply value_typing_extend_tenv_miss.
          - exact Hs.
          - intro Hinx.
            apply (Hfresh x Hinx).
            simpl. apply in_or_app. right. simpl. left. reflexivity.
        }
        assert (Hs_ext :
          has_type FDs DI (((x, LocTy tc1 l1 r1) :: prefix ++ Gamma)%list)
                   (extend_store Sigma (l1, r1) tc1) C A' N' A' N' (e_val s) uty).
        { eapply value_typing_any_context.
          - exact Hs_mid.
          - intros y. reflexivity.
          - intros lr tc' Hin. simpl. right. exact Hin.
        }
        eapply IH2
          with (prefix := (x, LocTy tc1 l1 r1) :: prefix)
               (z := z) (uty := uty) (Gamma := Gamma) (s := s).
        -- reflexivity.
        -- simpl. destruct (term_var_eq_dec z x); [contradiction | exact Hnone].
        -- exact Hs_ext.
        -- intros y Hy Hin.
           apply (Hfresh y Hy).
           simpl. apply in_or_app. right. simpl. right. exact Hin.
  - intros FDs DI G Sigma C A N A' N' r e t Hfresh Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh_s.
    subst G. simpl.
    eapply T_LRegion.
    + exact Hfresh.
    + eapply IH; eauto.
      eapply value_typing_any_context.
      * exact Hs.
      * intros y. reflexivity.
      * intros lr tc' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l r e tc' l' r'
      Halloc HfreshOut Hneq Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh_s.
    subst G. simpl.
    eapply T_LLStart; eauto.
    eapply IH; eauto.
    eapply value_typing_any_context.
    + exact Hs.
    + intros y. reflexivity.
    + intros lr tc'' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l lprev r e tc'' l'' r''
      Halloc Hnur HfreshOut Hneq Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh_s.
    subst G. simpl.
    eapply T_LLTag; eauto.
    eapply IH; eauto.
    eapply value_typing_any_context.
    + exact Hs.
    + intros y. reflexivity.
    + intros lr tc' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l l1 r tc_prev e tc' l' r'
      Halloc Hstore Hnotin HfreshOut Hneq Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh_s.
    subst G. simpl.
    eapply T_LLAfter; eauto.
    eapply IH; eauto.
    eapply value_typing_any_context.
    + exact Hs.
    + intros y. reflexivity.
    + intros lr tc'' Hin. exact Hin.
  - intros FDs DI G Sigma C A N dc l r vs tc fieldtcs fields
      Hdc Hnur Hfields Hlayout Hfocus Hvals IHvals.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl.
    eapply T_DataCon; eauto.
  - intros FDs DI G Sigma C A N f lrs vs tc l r f_locs f_params f_retty
      f_regions f_body Hfd Hnur Halloc Hlen1 Hlen2 Hargs IHargs.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl.
    eapply T_App; eauto.
  - intros FDs DI G Sigma C A N A' N' scrut ps tc_s l_s r_s t
      Hscrut IHscrut Hcover Hps IHps.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. rewrite subst_val_case.
    assert (Hfresh_scrut :
      forall y, In y (val_term_vars s) -> ~ In y (expr_bound_term_vars (e_val scrut))).
    { intros y Hy Hin. simpl in Hin. contradiction. }
    assert (Hfresh_ps :
      forall y, In y (val_term_vars s) -> ~ In y (pats_bound_term_vars ps)).
    { intros y Hy Hin. apply (Hfresh y Hy). simpl. exact Hin. }
    eapply T_Case.
    + eapply IHscrut; eauto.
    + eapply pats_cover_subst_pats_val. exact Hcover.
    + eapply IHps; eauto.
  - intros FDs DI G Sigma C A N r.
    unfold subst_field_vals_case.
    intros prefix z uty Gamma s HG Hnone Hs.
    subst G. simpl. constructor.
  - intros FDs DI G Sigma C A N r vl fld vs flds Hhead IHhead Htail IHtail.
    unfold subst_field_vals_case.
    intros prefix z uty Gamma s HG Hnone Hs.
    subst G. simpl.
    eapply T_FieldValsCons.
    + eapply IHhead; eauto.
    + eapply IHtail; eauto.
  - intros FDs DI G Sigma C A N formals actuals.
    unfold subst_app_vals_case.
    intros prefix z uty Gamma s HG Hnone Hs.
    subst G. simpl. constructor.
  - intros FDs DI G Sigma C A N formals actuals vl param vs params
      Hhead IHhead Htail IHtail.
    unfold subst_app_vals_case.
    intros prefix z uty Gamma s HG Hnone Hs.
    subst G. simpl.
    eapply T_AppValsCons.
    + eapply IHhead; eauto.
    + eapply IHtail; eauto.
  - intros FDs DI tc_s G Sigma C A N A' N' dc binds body tc fieldtcs tc_res l r
      Hdc Htc Hfields Hstore Hbody IHbody.
    unfold subst_pat_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl.
    destruct
      (existsb
         (fun b : term_var * ty =>
            if term_var_eq_dec z (fst b) then true else false)
         binds) eqn:Hbinds; simpl.
    + replace
        (existsb
           (fun b : term_var * located_type =>
              if term_var_eq_dec z (fst b) then true else false)
           binds)
        with true by (symmetry; exact Hbinds).
      simpl.
      eapply T_Pat; eauto.
      eapply expr_has_type_tenv_equiv.
      * exact Hbody.
      * apply tenv_equiv_shadow_under_binds_prefix. exact Hbinds.
    + replace
        (existsb
           (fun b : term_var * located_type =>
              if term_var_eq_dec z (fst b) then true else false)
           binds)
        with false by (symmetry; exact Hbinds).
      simpl.
      eapply T_Pat; eauto.
      replace (extend_tenv_list ((prefix ++ Gamma)%list) binds)
        with ((extend_tenv_list prefix binds ++ Gamma)%list).
      * eapply IHbody
          with (prefix := extend_tenv_list prefix binds)
               (z := z) (uty := uty) (Gamma := Gamma) (s := s).
        -- repeat rewrite extend_tenv_list_rev.
           rewrite <- app_assoc. reflexivity.
        -- apply lookup_tenv_extend_tenv_list_miss; assumption.
        -- eapply value_typing_any_context.
           ++ eapply value_typing_extend_tenv_list_disjoint.
              ** exact Hs.
              ** intros x t HinBind Hinx.
                 apply (Hfresh x Hinx). simpl. apply in_or_app. left.
                 change (In x (pat_term_vars binds)).
                 eapply in_map with (f := fst) in HinBind.
                 exact HinBind.
           ++ intros y.
              repeat rewrite extend_tenv_list_rev.
              rewrite <- app_assoc.
              reflexivity.
           ++ intros ent tc' Hin. apply in_extend_store_list. exact Hin.
        -- intros y Hy HinBody.
           apply (Hfresh y Hy). simpl. apply in_or_app. right. exact HinBody.
      * repeat rewrite extend_tenv_list_rev.
        rewrite <- app_assoc. reflexivity.
  - intros FDs DI tc_s G Sigma C A N t.
    unfold subst_pats_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl. constructor.
  - intros FDs DI tc_s G Sigma C A N A1 N1 A2 N2 t p ps Hpat IHpat Hps IHps.
    unfold subst_pats_case.
    intros prefix z uty Gamma s HG Hnone Hs Hfresh.
    subst G. simpl.
    eapply T_PatsCons.
    + eapply IHpat; eauto.
      intros y Hy HinPat.
      apply (Hfresh y Hy). simpl. apply in_or_app. left. exact HinPat.
    + eapply IHps.
      * reflexivity.
      * exact Hnone.
      * eapply value_typing_any_context.
        -- exact Hs.
        -- intros y. reflexivity.
        -- intros lr tc' Hin. exact Hin.
      * intros y Hy HinPs.
        apply (Hfresh y Hy). simpl. apply in_or_app. right. exact HinPs.
Qed.

Lemma substitution_val :
  forall FDs DI Gamma x vty Sigma C A N A' N' e T v0,
    has_type FDs DI (cons (x, vty) Gamma) Sigma C A N A' N' e T ->
    has_type FDs DI Gamma Sigma C A N A N (e_val v0) vty ->
    (forall y, In y (val_term_vars v0) -> ~ In y (expr_bound_term_vars e)) ->
    has_type FDs DI Gamma Sigma C A N A' N' (subst_val x v0 e) T.
Proof.
  intros FDs DI Gamma x vty Sigma C A N A' N' e T v0 HT Hs Hfresh.
  destruct substitution_val_mutual as [Hex _].
  eapply Hex with (prefix := nil) (z := x) (uty := vty) (Gamma := Gamma) (s := v0); eauto.
Qed.

Lemma preservation_let_val_case :
  forall FDs DI Sigma C A N Aout Nout M S x T1 vl e2 T,
    has_type FDs DI nil Sigma C A N Aout Nout (e_let x T1 (e_val vl) e2) T ->
    store_wf DI Sigma C A N M S ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout
               (subst_val x vl e2) T
      /\ store_wf DI Sigma' C' Ain' Nin' M S
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  intros FDs DI Sigma C A N Aout Nout M S x T1 vl e2 T Hty Hwf.
  inversion Hty; subst.
  destruct (has_type_value_same_io _ _ _ _ _ _ _ _ _ _ _ H13) as [HA' HN'].
  subst A' N'.
  inversion H13; subst.
  - simpl in H11. discriminate.
  - exists (extend_store Sigma (l1, r1) tc1), C, A, N.
    split.
    + eapply substitution_val.
      * exact H14.
      * apply T_ConcreteLoc. simpl. auto.
      * intros y Hy. inversion Hy.
    + split.
      * eapply store_wf_extend_store_existing.
        -- exact Hwf.
        -- exact H10.
      * split.
        -- intros lr tc Hin. right. exact Hin.
        -- apply conloc_extends_refl.
Qed.

Lemma preservation_letregion_case :
  forall FDs DI Sigma C A N Aout Nout M S r body T,
    has_type FDs DI nil Sigma C A N Aout Nout (e_letregion r body) T ->
    store_wf DI Sigma C A N M S ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout body T
      /\ store_wf DI Sigma' C' Ain' Nin' M S
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  intros FDs DI Sigma C A N Aout Nout M S r body T Hty Hwf.
  inversion Hty; subst.
  exists Sigma, C, (extend_alloc A r AP_None), N.
  split.
  - exact H12.
  - split.
    + eapply store_wf_extend_alloc_none_fresh; eauto.
    + split.
      * apply store_extends_refl.
      * apply conloc_extends_refl.
Qed.

Lemma preservation_letloc_start_case :
  forall FDs DI Sigma C A N Aout Nout M S l r body T,
    has_type FDs DI nil Sigma C A N Aout Nout
             (e_letloc l r (LE_Start r) body) T ->
    has_type_fresh FDs DI nil Sigma C A N Aout Nout
                    (e_letloc l r (LE_Start r) body) T ->
    store_wf DI Sigma C A N M S ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout body T
      /\ store_wf DI Sigma' C' Ain' Nin' (extend_loc M (l, r) (r, 0)) S
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  intros FDs DI Sigma C A N Aout Nout M S l r body T Hty Hfresh Hwf.
  inversion Hty; subst. clear Hty.
  inversion Hfresh; subst. clear Hfresh.
  exists Sigma,
         (extend_conloc C (l, r) (LE_Start r)),
         (extend_alloc A r (AP_Loc (l, r))),
         (extend_nursery N (l, r)).
  split.
  - match goal with
    | [ Hbody : has_type _ _ _ _ _ _ _ _ _ body _ |- _ ] => exact Hbody
    end.
  - split.
    + eapply store_wf_extend_letloc_start; eauto.
    + split.
      * apply store_extends_refl.
      * intros lr le Hin.
        simpl. right. exact Hin.
Qed.

Lemma preservation_letloc_tag_case :
  forall FDs DI Sigma C A N Aout Nout M S l lprev r body T rc i,
    has_type FDs DI nil Sigma C A N Aout Nout
             (e_letloc l r (LE_Next lprev r) body) T ->
    has_type_fresh FDs DI nil Sigma C A N Aout Nout
                    (e_letloc l r (LE_Next lprev r) body) T ->
    store_wf DI Sigma C A N M S ->
    lookup_loc M (lprev, r) = Some (rc, i) ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout body T
      /\ store_wf DI Sigma' C' Ain' Nin' (extend_loc M (l, r) (rc, i + 1)) S
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  intros FDs DI Sigma C A N Aout Nout M S l lprev r body T rc i
         Hty Hfresh Hwf Hlookup.
  inversion Hty; subst; clear Hty.
  inversion Hfresh; subst; clear Hfresh.
  pose proof Hwf as Hwf_copy.
  destruct Hwf_copy as [_ [_ [Halloc _]]].
  destruct Halloc as [Hlin1 _].
  match goal with
  | [ Hfocus : In (r, AP_Loc (lprev, r)) A,
      Hnur : In (lprev, r) N |- _ ] =>
      destruct (Hlin1 r lprev Hfocus Hnur) as [i0 [Hlk0 Hgt0]]
  end.
  rewrite Hlookup in Hlk0. inversion Hlk0; subst rc i0.
  exists Sigma,
         (extend_conloc C (l, r) (LE_Next lprev r)),
         (extend_alloc A r (AP_Loc (l, r))),
         (extend_nursery N (l, r)).
  split.
  - match goal with
    | [ Hbody : has_type _ _ _ _ _ _ _ _ _ body _ |- _ ] => exact Hbody
    end.
  - split.
    + eapply store_wf_extend_letloc_tag; eauto.
    + split.
      * apply store_extends_refl.
      * intros lr le Hin.
        simpl. right. exact Hin.
Qed.

Lemma preservation_letloc_after_case :
  forall FDs DI Sigma C A N Aout Nout M S l l1 r tc_prev body T rc i j,
    has_type FDs DI nil Sigma C A N Aout Nout
             (e_letloc l r (LE_After tc_prev l1 r) body) T ->
    has_type_fresh FDs DI nil Sigma C A N Aout Nout
                    (e_letloc l r (LE_After tc_prev l1 r) body) T ->
    store_wf DI Sigma C A N M S ->
    lookup_loc M (l1, r) = Some (rc, i) ->
    end_witness DI S (rc, i) tc_prev (rc, j) ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout body T
      /\ store_wf DI Sigma' C' Ain' Nin' (extend_loc M (l, r) (rc, j)) S
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  intros FDs DI Sigma C A N Aout Nout M S l l1 r tc_prev body T rc i j
         Hty Hfresh Hwf Hlookup Hew.
  inversion Hty; subst; clear Hty.
  inversion Hfresh; subst; clear Hfresh.
  pose proof Hwf as Hwf_copy.
  destruct Hwf_copy as [Hmap _].
  match goal with
  | [ Hstore_prev : In ((l1, r), tc_prev) Sigma |- _ ] =>
      destruct (Hmap l1 r tc_prev Hstore_prev) as [i0 [j0 [Hlk0 Hew0]]]
  end.
  rewrite Hlookup in Hlk0. inversion Hlk0; subst rc i0.
  exists Sigma,
         (extend_conloc C (l, r) (LE_After tc_prev l1 r)),
         (extend_alloc A r (AP_Loc (l, r))),
         (extend_nursery N (l, r)).
  split.
  - match goal with
    | [ Hbody : has_type _ _ _ _ _ _ _ _ _ body _ |- _ ] => exact Hbody
    end.
  - split.
    + eapply store_wf_extend_letloc_after; eauto.
    + split.
      * apply store_extends_refl.
      * intros lr le Hin.
        simpl. right. exact Hin.
Qed.

Lemma preserve_let_under_step :
  forall FDs DI Sigma C A' N' Aout Nout
         Sigma' C' Ain' Nin'
         x tc1 l1 r1 e1' e2 tc2 l2 r2,
    has_type FDs DI nil Sigma' C' Ain' Nin' A' N' e1'
             (LocTy tc1 l1 r1) ->
    has_type FDs DI (extend_tenv nil x (LocTy tc1 l1 r1))
             (extend_store Sigma (l1, r1) tc1)
             C A' N' Aout Nout e2 (LocTy tc2 l2 r2) ->
    store_extends Sigma Sigma' ->
    conloc_extends C C' ->
    has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout
             (e_let x (LocTy tc1 l1 r1) e1' e2) (LocTy tc2 l2 r2).
Proof.
  intros FDs DI Sigma C A' N' Aout Nout
         Sigma' C' Ain' Nin'
         x tc1 l1 r1 e1' e2 tc2 l2 r2 He1 Hbody Hse Hce.
  eapply T_Let.
  - exact He1.
  - eapply expr_has_type_sigma_c_monotone.
    + exact Hbody.
    + apply store_extends_extend_store. exact Hse.
    + exact Hce.
Qed.

Lemma preservation_let_expr_case :
  forall FDs DI Sigma C A' N' Aout Nout
         Sigma' C' Ain' Nin'
         M' S'
         x tc1 l1 r1 e1' e2 tc2 l2 r2,
    has_type FDs DI nil Sigma' C' Ain' Nin' A' N' e1'
             (LocTy tc1 l1 r1) ->
    has_type FDs DI (extend_tenv nil x (LocTy tc1 l1 r1))
             (extend_store Sigma (l1, r1) tc1)
             C A' N' Aout Nout e2 (LocTy tc2 l2 r2) ->
    store_wf DI Sigma' C' Ain' Nin' M' S' ->
    store_extends Sigma Sigma' ->
    conloc_extends C C' ->
    exists Sigma'' C'' Ain'' Nin'',
      has_type FDs DI nil Sigma'' C'' Ain'' Nin'' Aout Nout
               (e_let x (LocTy tc1 l1 r1) e1' e2) (LocTy tc2 l2 r2)
      /\ store_wf DI Sigma'' C'' Ain'' Nin'' M' S'
      /\ store_extends Sigma Sigma''
      /\ conloc_extends C C''.
Proof.
  intros FDs DI Sigma C A' N' Aout Nout
         Sigma' C' Ain' Nin'
         M' S'
         x tc1 l1 r1 e1' e2 tc2 l2 r2
         He1 Hbody Hwf Hse Hce.
  exists Sigma', C', Ain', Nin'.
  split.
  - eapply preserve_let_under_step; eauto.
  - split.
    + exact Hwf.
    + split; assumption.
Qed.

(* ================================================================= *)
(* Theorem: Progress  (thesis §2.2.3, Lemma Progress)                *)
(*                                                                    *)
(* A well-typed expression in an empty variable environment, with a   *)
(* well-formed store, is either a value or can take a step.           *)
(*                                                                    *)
(*   If  FDs;∅;Σ;C;A;N ⊢ A';N'; e : T                               *)
(*   and store_wf(DI, Σ, C, A, N, M, S)                              *)
(*   and di_functional(DI)                                            *)
(*   and expr_wf(M, e)                                                *)
(*   then  (∃ v, e = v)  ∨  (∃ S' M' e', S;M;e ⇒ S';M';e')         *)
(* ================================================================= *)

(* The main proof proceeds by induction on the typing derivation
   in a generalized form (arbitrary Γ with Γ = nil premise).  This
   avoids difficulties with Coq's induction tactic on non-variable
   indices. *)

Lemma progress_gen :
  forall FDs DI G Sigma C A N A2 N2 e Tl,
    has_type FDs DI G Sigma C A N A2 N2 e Tl ->
    G = @nil (term_var * ty) ->
    forall M St,
    store_wf DI Sigma C A N M St ->
    di_functional DI ->
    expr_wf M e ->
    (exists vl, e = e_val vl)
    \/ (exists St2 M2 e2, step FDs DI St M e St2 M2 e2).
Proof.
  intros FDs DI G Sigma C A N A2 N2 e Tl Htype.
  induction Htype; intros HG M St Hwf Hdi Hewf; subst.

  (* ---- T_Var ----
     Γ = nil, so In (x, _) nil is False. *)
  1: { exfalso. simpl in H. discriminate. }

  (* ---- T_ConcreteLoc ----
     e = e_val (v_cloc ...), already a value. *)
  1: { left. eauto. }

  (* ---- T_Let ----
     By IH on e1: if e1 is a value, step with D_Let_Val;
     otherwise step with D_Let_Expr. *)
  1: {
    right.
    simpl in Hewf; destruct Hewf as [He1 He2].
    destruct (IHHtype1 eq_refl M St Hwf Hdi He1)
      as [[vl Hval] | [St2 [M2 [e1' Hstep]]]].
    - subst. do 3 eexists. apply D_Let_Val.
    - do 3 eexists. apply D_Let_Expr.
      + destruct e1; try reflexivity. exfalso. inversion Hstep.
      + exact Hstep.
  }

  (* ---- T_LRegion ----
     Unconditionally steps with D_LetRegion. *)
  1: { right. do 3 eexists. apply D_LetRegion. }

  (* ---- T_LLStart ----
     Unconditionally steps with D_LetLoc_Start. *)
  1: { right. do 3 eexists. apply D_LetLoc_Start. }

  (* ---- T_LLTag ----
     From alloc_wf (write-once), (lprev,r) ∈ N gives
     M(lprev,r) = ⟨r,i⟩, so D_LetLoc_Tag applies. *)
  1: {
    right.
    destruct Hwf as [_ [_ [Halloc _]]].
    destruct Halloc as [_ [_ [Hwo _]]].
    destruct (Hwo lprev r H0) as [i [Hlk _]].
    do 3 eexists. eapply D_LetLoc_Tag. exact Hlk.
  }

  (* ---- T_LLAfter ----
     From map-store consistency, ((l1,r),tc_prev) ∈ Σ gives
     M(l1,r) = ⟨r,i⟩ and end_witness, so D_LetLoc_After applies. *)
  1: {
    right.
    destruct Hwf as [Hms _].
    destruct (Hms l1 r tc_prev H0) as [i [j [Hlk Hew]]].
    do 3 eexists. eapply D_LetLoc_After; eauto.
  }

  (* ---- T_DataCon ----
     From alloc_wf (write-once), (l,r) ∈ N gives
     M(l,r) = ⟨r,i⟩, so D_DataCon applies. *)
  1: {
    right.
    destruct Hwf as [_ [_ [Halloc _]]].
    destruct Halloc as [_ [_ [Hwo _]]].
    destruct (Hwo l r H0) as [i [Hlk _]].
    do 3 eexists. eapply D_DataCon. exact Hlk.
  }

  (* ---- T_App ----
     The function declaration is in FDs (from T_App premise),
     so In_lookup_fdecl gives lookup success for D_App. *)
  1: {
    right.
    destruct (In_lookup_fdecl _ _ _ _ _ _ _ H)
      as [l' [p' [t' [rg' [b' Hlk]]]]].
    do 3 eexists. eapply D_App. exact Hlk.
  }

  (* ---- T_Case ----
     Most complex case.  Chain of reasoning:
     1. Invert scrutinee typing (Γ=nil → only T_ConcreteLoc)
     2. val_wf connects v_cloc to M
     3. map-store consistency gives end_witness
     4. Invert end_witness to get tag K and field types
     5. pats_cover guarantees a matching pattern exists
     6. find_matching_pat succeeds
     7. pat_has_type_inv + di_functional align field types
     8. ewf_to_field_starts gives field offsets
     9. Apply D_Case *)
  1: {
    right.
    simpl in Hewf; destruct Hewf as [Hvwf _].
    (* 1. Invert scrutinee typing *)
    inversion Htype; subst.
    - (* T_Var: impossible in empty Γ *)
      match goal with [ Hlookup : lookup_tenv nil _ = Some _ |- _ ] =>
        simpl in Hlookup; discriminate end.
    - (* T_ConcreteLoc: scrut = v_cloc r0 i l r *)
      simpl in Hvwf.
      (* 2-3. map-store consistency *)
      destruct Hwf as [Hms _].
      match goal with [ HinS : In ((_, _), _) _ |- _ ] =>
        destruct (Hms _ _ _ HinS) as [i' [j [Hlk Hew]]]
      end.
      rewrite Hvwf in Hlk. inversion Hlk; subst.
      (* 4. Invert end_witness to get tag lookup and field info *)
      inversion Hew; subst.
      (* 5. pats_cover guarantees a matching pattern for K *)
      match goal with [ Hlookup : lookup_datacon _ _ = Some _ |- _ ] =>
        apply lookup_datacon_In in Hlookup as HinDI
      end.
      destruct (H K fieldtys HinDI) as [b0 [bd0 Hin]].
      (* 6. find_matching_pat succeeds *)
      destruct (In_find_matching_pat _ _ _ _ Hin) as [b' [bd' Hfind]].
      (* 7. The found pattern is typed; extract constructor info *)
      apply find_matching_pat_In in Hfind as HinPs.
      destruct (pats_have_type_In _ _ _ _ _ _ _ _ _ _ _ _ _ H0 HinPs)
        as [A1 [N1 [A3 [N3 Hpty]]]].
      destruct (pat_has_type_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpty)
        as [tc_p [ftc_p [HinDI_p [Htceq Hpft]]]].
      (* di_functional: constructor info is unique *)
      assert (Heq : (tc_s, fieldtys) = (tc_p, ftc_p))
        by (apply Hdi with K; [exact HinDI | subst; exact HinDI_p]).
      inversion Heq; subst.
      (* 8. end_witness_fields gives field_starts *)
      match goal with [ Hewf : end_witness_fields _ _ _ _ _ _ |- _ ] =>
        destruct (ewf_to_field_starts _ _ _ _ _ _ Hewf) as [indices Hfs]
      end.
      (* 9. Assemble D_Case *)
      do 3 eexists. eapply D_Case; eauto.
  }

  (* Auxiliary goals from mutual induction (pat_has_type, pats_have_type).
     These are trivially satisfied since we only need progress for
     has_type, not for the pattern typing judgments. *)
  all: intros; left; eauto.
Qed.

Theorem progress :
  forall FDs DI Sigma C A N A' N' M S e T,
    has_type FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    di_functional DI ->
    expr_wf M e ->
    (exists v0, e = e_val v0)
    \/ (exists S' M' e', step FDs DI S M e S' M' e').
Proof.
  intros. eapply progress_gen; eassumption || reflexivity.
Qed.

(* ================================================================= *)
(* Theorem: Preservation  (mechanized restatement of thesis §2.2.3)  *)
(*                                                                    *)
(* The thesis statement reuses A'/N' as though the reduct were always *)
(* typed under the output environments of the source expression.      *)
(* That is not true for this judgmental presentation: rules such as   *)
(* T_Let, T_LLStart/T_LLTag/T_LLAfter, and T_Case step to subterms    *)
(* whose typing lives under intermediate premise environments.        *)
(*                                                                    *)
(* So the mechanized preservation lemma returns the reduct together   *)
(* with the input environments it actually inhabits, while keeping    *)
(* the source judgment's output environments fixed.  This is the      *)
(* shape needed to rebuild enclosing rules like T_Let.                *)
(* ================================================================= *)

Theorem preservation :
  forall FDs DI Sigma C A N Aout Nout M S e T S' M' e',
    Forall (fdecl_has_type FDs DI) FDs ->
    has_type FDs DI nil Sigma C A N Aout Nout e T ->
    has_type_fresh FDs DI nil Sigma C A N Aout Nout e T ->
    store_wf DI Sigma C A N M S ->
    step FDs DI S M e S' M' e' ->
    exists Sigma' C' Ain' Nin',
      has_type FDs DI nil Sigma' C' Ain' Nin' Aout Nout e' T
      /\ store_wf DI Sigma' C' Ain' Nin' M' S'
      /\ store_extends Sigma Sigma'
      /\ conloc_extends C C'.
Proof.
  (* By rule induction on the step derivation.
     Key cases:
       D_DataCon —
         Σ' = Σ ∪ {(l,r) ↦ T}.
         Typing: by T_ConcreteLoc with the extended Σ'.
         Store WF:
           map-store consistency for (l,r): construct end-witness
             from field typing + constr_app_wf.
           map-store consistency for others: end-witness preserved
             because write-once ensures no overlap.
           alloc_wf: nursery shrinks (remove (l,r)), allocptr shifts.
           dom(Σ') ∩ N' = ∅: (l,r) removed from N'.

       D_LetLoc_Start / D_LetLoc_Tag / D_LetLoc_After —
         Σ' = Σ, C' updated with new constraint.
         Typing: directly from typing inversion.
         Store WF: constr_app_wf extended, alloc_wf maintained
           via allocptr reasoning.

       D_Let_Val —
         Apply substitution lemma.
         Store WF unchanged (S, M not modified).

       D_Let_Expr —
         IH on the stepped sub-expression, then rebuild T_Let.

       D_Case —
         Σ' extended with field location types.
         Apply substitution lemma for pattern variables.
         Store WF: M extended but S unchanged; field locations
           get end-witness from scrutinee's end-witness.

       D_App —
         Apply substitution/value-location instantiation for the callee body.
         Store WF unchanged.

       D_LetRegion —
         Straightforward; store and M unchanged. *)
Admitted.

(* ================================================================= *)
(* Theorem: Type Safety  (thesis §2.2.3, Theorem Type Safety)        *)
(*                                                                    *)
(* Combining Progress and Preservation: a well-typed program that     *)
(* takes any number of steps never gets stuck.                        *)
(*                                                                    *)
(*   If  ∅;Σ;C;A;N ⊢ A';N'; e : T                                  *)
(*   and store_wf(DI, Σ, C, A, N, M, S)                              *)
(*   and S;M;e ⇒* Sₙ;Mₙ;eₙ                                        *)
(*   then (∃ v, eₙ = v) ∨ (∃ S' M' e', Sₙ;Mₙ;eₙ ⇒ S';M';e')      *)
(* ================================================================= *)

Theorem type_safety :
  forall FDs DI Sigma C A N A' N' M S e T Sn Mn en,
    Forall (fdecl_has_type FDs DI) FDs ->
    has_type FDs DI nil Sigma C A N A' N' e T ->
    has_type_fresh FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    di_functional DI ->
    expr_wf M e ->
    multi_step FDs DI S M e Sn Mn en ->
    (exists v0, en = e_val v0)
    \/ (exists S' M' e', step FDs DI Sn Mn en S' M' e').
Proof.
  (* By induction on multi_step:
     - MS_refl: apply progress.
     - MS_step: apply preservation to get new typing + store_wf,
                then apply IH. *)
Admitted.

End LoCalSafety.
