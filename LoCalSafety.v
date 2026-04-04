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
    store_find_heap S r = None).

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

Scheme has_type_ind' := Induction for has_type Sort Prop
with pat_has_type_ind' := Induction for pat_has_type Sort Prop
with pats_have_type_ind' := Induction for pats_have_type Sort Prop.

Combined Scheme typing_mutind
  from has_type_ind', pat_has_type_ind', pats_have_type_ind'.

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
  apply typing_mutind.
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
  - intros FDs DI G S0 C A N A' N' r e t Hty IH G' Heq.
    eapply T_LRegion. apply IH. exact Heq.
  - intros FDs DI G S0 C A N A'' N'' l r e tc' l' r' Hnone Hfresh Hneq
      Hty IH G' Heq.
    eapply T_LLStart; eauto.
  - intros FDs DI G S0 C A N A'' N'' l lprev r e tc'' l'' r''
      Halloc Hnur Hfresh Hneq Hty IH G' Heq.
    eapply T_LLTag; eauto.
  - intros FDs DI G S0 C A N A'' N'' l l1 r tc_prev e tc' l' r'
      Halloc Hstore Hnotin Hfresh Hneq Hty IH G' Heq.
    eapply T_LLAfter; eauto.
  - intros FDs DI G S0 C A N dc l r vs tc fieldtcs Hdc Hnur Hlen G' Heq.
    eapply T_DataCon; eauto.
  - intros FDs DI G S0 C A N f lrs vs tc l r f_locs f_params f_retty
      f_regions f_body Hfd Hnur Halloc Hlen1 Hlen2 G' Heq.
    eapply T_App; eauto.
  - intros FDs DI G S0 C A N A' N' scrut ps tc_s l_s r_s t
      Hscrut IHscrut Hcover Hps IHps G' Heq.
    eapply T_Case.
    + apply IHscrut. exact Heq.
    + exact Hcover.
    + apply IHps. exact Heq.
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

Lemma existsb_bind_hit :
  forall x (binds : list term_binding),
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
  forall x (binds : list term_binding) t,
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
(* expression preserves typing.  Simplified single-variable form.     *)
(* The full thesis version handles simultaneous value + location      *)
(* substitution.                                                      *)
(* ================================================================= *)

Definition subst_expr_case
    FDs DI G Sigma C A N A' N' e T
    (HT : has_type FDs DI G Sigma C A N A' N' e T) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI nil Sigma C A N A N (e_val s) uty ->
    has_type FDs DI (prefix ++ Gamma)%list Sigma C A N A' N' (subst_val z s e) T.

Definition subst_pat_case
    FDs DI tc_s G Sigma C A N A' N' T p
    (HT : pat_has_type FDs DI tc_s G Sigma C A N A' N' T p) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI nil Sigma C A N A N (e_val s) uty ->
    pat_has_type FDs DI tc_s (prefix ++ Gamma)%list Sigma C A N A' N' T (subst_pat_val z s p).

Definition subst_pats_case
    FDs DI tc_s G Sigma C A N A' N' T ps
    (HT : pats_have_type FDs DI tc_s G Sigma C A N A' N' T ps) : Prop :=
  forall prefix z uty Gamma s,
    G = ((prefix ++ (z, uty) :: Gamma)%list) ->
    lookup_tenv prefix z = None ->
    has_type FDs DI nil Sigma C A N A N (e_val s) uty ->
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
  apply typing_mutind.
  - intros FDs DI G Sigma C A N x tc l r Hlookup Hstore.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
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
        eapply closed_value_typing_any_context.
        -- exact Hclosed.
        -- intros lr tc' Hin. exact Hin.
      * simpl. destruct (term_var_eq_dec z x) as [Heqzx | Hneqzx].
        { exfalso. apply Hneq. symmetry. exact Heqzx. }
        apply T_Var.
        -- rewrite lookup_tenv_app. rewrite Hprefix. simpl.
           destruct (term_var_eq_dec x z); [contradiction | exact Hlookup].
        -- exact Hstore.
  - intros FDs DI G Sigma C A N r0 i l r tc Hstore.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl. apply T_ConcreteLoc. exact Hstore.
  - intros FDs DI G Sigma C A N A' N' A'' N'' x e1 e2 tc1 l1 r1 tc2 l2 r2
      Hty1 IH1 Hty2 IH2.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
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
        eapply IH2
          with (prefix := (x, LocTy tc1 l1 r1) :: prefix)
               (z := z) (uty := uty) (Gamma := Gamma) (s := s).
        -- reflexivity.
        -- simpl. destruct (term_var_eq_dec z x); [contradiction | exact Hnone].
        -- eapply closed_value_typing_any_context.
           ++ exact Hclosed.
           ++ intros lr tc' Hin. simpl. right. exact Hin.
  - intros FDs DI G Sigma C A N A' N' r e t Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_LRegion.
    eapply IH; eauto.
    eapply closed_value_typing_any_context.
    + exact Hclosed.
    + intros lr tc' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l r e tc' l' r' Halloc Hfresh Hneq
      Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_LLStart; eauto.
    eapply IH; eauto.
    eapply closed_value_typing_any_context.
    + exact Hclosed.
    + intros lr tc'' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l lprev r e tc'' l'' r''
      Halloc Hnur Hfresh Hneq Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_LLTag; eauto.
    eapply IH; eauto.
    eapply closed_value_typing_any_context.
    + exact Hclosed.
    + intros lr tc' Hin. exact Hin.
  - intros FDs DI G Sigma C A N A'' N'' l l1 r tc_prev e tc' l' r'
      Halloc Hstore Hnotin Hfresh Hneq Hty IH.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_LLAfter; eauto.
    eapply IH; eauto.
    eapply closed_value_typing_any_context.
    + exact Hclosed.
    + intros lr tc'' Hin. exact Hin.
  - intros FDs DI G Sigma C A N dc l r vs tc fieldtcs Hdc Hnur Hlen.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_DataCon; eauto.
    rewrite map_length. exact Hlen.
  - intros FDs DI G Sigma C A N f lrs vs tc l r f_locs f_params f_retty
      f_regions f_body Hfd Hnur Halloc Hlen1 Hlen2.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_App; eauto.
    rewrite map_length. exact Hlen2.
  - intros FDs DI G Sigma C A N A' N' scrut ps tc_s l_s r_s t
      Hscrut IHscrut Hcover Hps IHps.
    unfold subst_expr_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. rewrite subst_val_case.
    eapply T_Case.
    + eapply IHscrut; eauto.
    + eapply pats_cover_subst_pats_val. exact Hcover.
    + eapply IHps; eauto.
  - intros FDs DI tc_s G Sigma C A N A' N' dc binds body tc fieldtcs tc_res l r
      Hdc Htc Hfields Hstore Hbody IHbody.
    unfold subst_pat_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    destruct
      (existsb
         (fun b : term_binding =>
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
        -- eapply closed_value_typing_any_context.
           ++ exact Hclosed.
           ++ intros ent tc' Hin. apply in_extend_store_list. exact Hin.
      * repeat rewrite extend_tenv_list_rev.
        rewrite <- app_assoc. reflexivity.
  - intros FDs DI tc_s G Sigma C A N t.
    unfold subst_pats_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl. constructor.
  - intros FDs DI tc_s G Sigma C A N A1 N1 A2 N2 t p ps Hpat IHpat Hps IHps.
    unfold subst_pats_case.
    intros prefix z uty Gamma s HG Hnone Hclosed.
    subst G. simpl.
    eapply T_PatsCons.
    + eapply IHpat; eauto.
    + eapply IHps; eauto.
      eapply closed_value_typing_any_context.
      * exact Hclosed.
      * intros lr tc' Hin. exact Hin.
Qed.

Lemma substitution_val :
  forall FDs DI Gamma x vty Sigma C A N A' N' e T v0,
    has_type FDs DI (cons (x, vty) Gamma) Sigma C A N A' N' e T ->
    has_type FDs DI nil Sigma C A N A N (e_val v0) vty ->
    has_type FDs DI Gamma Sigma C A N A' N' (subst_val x v0 e) T.
Proof.
  intros FDs DI Gamma x vty Sigma C A N A' N' e T v0 HT Hclosed.
  destruct substitution_val_mutual as [Hex _].
  eapply Hex with (prefix := nil) (z := x) (uty := vty) (Gamma := Gamma) (s := v0); eauto.
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
    G = @nil term_binding ->
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
    destruct Hwf as [_ [_ [[_ [_ [Hwo _]]] _]]].
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
    destruct Hwf as [_ [_ [[_ [_ [Hwo _]]] _]]].
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
(* Theorem: Preservation  (thesis §2.2.3, Lemma Preservation)        *)
(*                                                                    *)
(* If a well-typed expression takes a step under a well-formed store, *)
(* the result is well-typed under (possibly extended) environments    *)
(* and the new store remains well-formed.                             *)
(*                                                                    *)
(*   If  ∅;Σ;C;A;N ⊢ A';N'; e : T                                  *)
(*   and store_wf(DI, Σ, C, A, N, M, S)                              *)
(*   and S;M;e ⇒ S';M';e'                                           *)
(*   then ∃ Σ'⊇Σ, C',                                               *)
(*     ∅;Σ';C';A';N' ⊢ A'';N''; e' : T                              *)
(*     and store_wf(DI, Σ', C', A', N', M', S')                      *)
(* ================================================================= *)

Theorem preservation :
  forall FDs DI Sigma C A N A' N' M S e T S' M' e',
    has_type FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    step FDs DI S M e S' M' e' ->
    exists Sigma' C' A'' N'',
      has_type FDs DI nil Sigma' C' A' N' A'' N'' e' T
      /\ store_wf DI Sigma' C' A' N' M' S'
      /\ (forall lr T0, In (lr, T0) Sigma -> In (lr, T0) Sigma').
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
         IH on sub-expression step.

       D_Case —
         Σ' extended with field location types.
         Apply substitution lemma for pattern variables.
         Store WF: M extended but S unchanged; field locations
           get end-witness from scrutinee's end-witness.

       D_App —
         Apply substitution lemma (values + locations).
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
    has_type FDs DI nil Sigma C A N A' N' e T ->
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
