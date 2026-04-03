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

Module Import Syn := LoCalSyntax.LoCalSyntax.

(* We access Static and Dynamic via qualified names to avoid
   ambiguity for identifiers defined in both (laddr, datacon_info,
   eq_dec lemmas). *)

Module Stat := LoCalStatic.LoCalStatic.
Module Dyn  := LoCalDynamic.LoCalDynamic.

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

Fixpoint max_heap_index (h : Dyn.heap) : option nat :=
  match h with
  | nil => None
  | (i, _) :: h' =>
      match max_heap_index h' with
      | None => Some i
      | Some j => Some (Nat.max i j)
      end
  end.

Definition allocptr (S : Dyn.store) (r : region_var) : option nat :=
  match Dyn.store_find_heap S r with
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
    (DI : Dyn.datacon_info)
    (C  : Stat.conloc_env)
    (M  : Dyn.loc_map)
    (S  : Dyn.store) : Prop :=

  (* Rule 1 — constraint-start:
     (l^r ↦ start(r)) ∈ C  ⟹  M(l^r) = ⟨r, 0⟩ *)
  (forall l r,
    In ((l, r), LE_Start r) C ->
    Dyn.lookup_loc M (l, r) = Some (r, 0))
  /\
  (* Rule 2 — constraint-tag:
     (l^r ↦ l'^r + 1) ∈ C  ⟹
       ∃ i, M(l'^r) = ⟨r, i⟩  ∧  M(l^r) = ⟨r, i+1⟩ *)
  (forall l r l',
    In ((l, r), LE_Next l' r) C ->
    exists i,
      Dyn.lookup_loc M (l', r) = Some (r, i) /\
      Dyn.lookup_loc M (l, r) = Some (r, i + 1))
  /\
  (* Rule 3 — constraint-after:
     (l^r ↦ after(T@l'^r)) ∈ C  ⟹
       ∃ i j, M(l'^r) = ⟨r,i⟩ ∧ ewitness(T,⟨r,i⟩,S,⟨r,j⟩)
              ∧ M(l^r) = ⟨r,j⟩ *)
  (forall l r T l',
    In ((l, r), LE_After T l' r) C ->
    exists i j,
      Dyn.lookup_loc M (l', r) = Some (r, i) /\
      Dyn.end_witness DI S (r, i) T (r, j) /\
      Dyn.lookup_loc M (l, r) = Some (r, j)).

(* ================================================================= *)
(* Allocation well-formedness                                         *)
(*   A ; N ⊢_{wf_ca}  M ; S                                         *)
(* (thesis §2.2.3 — write-once / linear-allocation invariant)        *)
(* ================================================================= *)

Definition alloc_wf
    (DI : Dyn.datacon_info)
    (A  : Stat.alloc_env)
    (N  : Stat.nursery)
    (M  : Dyn.loc_map)
    (S  : Dyn.store) : Prop :=

  (* Rule 1 — linear-alloc (in-flight):
     (r ↦ (l,r)) ∈ A  ∧  (l,r) ∈ N  ⟹
       ∃ i, M(l,r) = ⟨r,i⟩  ∧  i > allocptr(r,S) *)
  (forall r l,
    In (r, Stat.AP_Loc (l, r)) A ->
    In (l, r) N ->
    exists i,
      Dyn.lookup_loc M (l, r) = Some (r, i) /\
      gt_allocptr i (allocptr S r))
  /\
  (* Rule 2 — linear-alloc2 (fully allocated):
     (r ↦ (l,r)) ∈ A  ∧  M(l,r) = ⟨r,i⟩  ∧  (l,r) ∉ N
       ∧  ewitness(T,⟨r,i⟩,S,⟨r,j⟩)
       ⟹  j > allocptr(r,S) *)
  (forall r l i T j,
    In (r, Stat.AP_Loc (l, r)) A ->
    Dyn.lookup_loc M (l, r) = Some (r, i) ->
    ~ In (l, r) N ->
    Dyn.end_witness DI S (r, i) T (r, j) ->
    gt_allocptr j (allocptr S r))
  /\
  (* Rule 3 — write-once:
     (l,r) ∈ N  ⟹  ∃ i, M(l,r) = ⟨r,i⟩  ∧  S(r)(i) = None *)
  (forall l r,
    In (l, r) N ->
    exists i,
      Dyn.lookup_loc M (l, r) = Some (r, i) /\
      Dyn.heap_lookup S r i = None)
  /\
  (* Rule 4 — empty-region:
     (r ↦ ∅) ∈ A  ⟹  r ∉ dom(S) *)
  (forall r,
    In (r, Stat.AP_None) A ->
    Dyn.store_find_heap S r = None).

(* ================================================================= *)
(* Store well-formedness  (main judgment)                             *)
(*   Σ ; C ; A ; N  ⊢_wf  M ; S                                    *)
(* (thesis §2.2.3, Definition)                                       *)
(* ================================================================= *)

Definition store_wf
    (DI    : Dyn.datacon_info)
    (Sigma : Stat.store_type)
    (C     : Stat.conloc_env)
    (A     : Stat.alloc_env)
    (N     : Stat.nursery)
    (M     : Dyn.loc_map)
    (S     : Dyn.store) : Prop :=

  (* Rule 1 — map-store consistency:
     ∀ (l,r) ↦ T ∈ Σ,
       ∃ i j, M(l,r) = ⟨r,i⟩ ∧ ewitness(T, ⟨r,i⟩, S, ⟨r,j⟩) *)
  (forall l r T,
    In ((l, r), T) Sigma ->
    exists i j,
      Dyn.lookup_loc M (l, r) = Some (r, i) /\
      Dyn.end_witness DI S (r, i) T (r, j))
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
      Dyn.lookup_fdecl FDs f = Some (FunDecl f l' p' t' rg' b').
Proof.
  induction FDs as [| [f0 l0 p0 t0 rg0 b0] FDs' IH];
    intros f locs params retty regions body Hin.
  - inversion Hin.
  - simpl. destruct (Dyn.fun_var_eq_dec f f0).
    + subst. do 5 eexists. reflexivity.
    + destruct Hin as [Heq | Hin].
      * inversion Heq; subst. congruence.
      * eapply IH. exact Hin.
Qed.

(* ================================================================= *)
(* Additional invariants needed for progress                          *)
(* ================================================================= *)

(* Each constructor maps to unique info in DI. *)
Definition di_functional (DI : Dyn.datacon_info) : Prop :=
  forall K info1 info2,
    In (K, info1) DI -> In (K, info2) DI -> info1 = info2.

(* Concrete location values are consistent with the location map. *)
Definition val_wf (M : Dyn.loc_map) (vl : val) : Prop :=
  match vl with
  | v_var _ => True
  | v_cloc r0 i l r => Dyn.lookup_loc M (l, r) = Some (r0, i)
  end.

(* All concrete location values in an expression are consistent. *)
Fixpoint expr_wf (M : Dyn.loc_map) (e : expr) {struct e} : Prop :=
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
  Dyn.lookup_datacon DI K = Some info -> In (K, info) DI.
Proof.
  induction DI as [|[K' info'] DI' IH]; intros; simpl in *.
  - discriminate.
  - destruct (Dyn.datacon_eq_dec K K').
    + inversion H; subst. left; reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma In_find_matching_pat : forall K pats binds body,
  In (pat_clause K binds body) pats ->
  exists binds' body',
    Dyn.find_matching_pat K pats = Some (pat_clause K binds' body').
Proof.
  intros K pats. induction pats as [|[K' b' bd'] pats' IH];
    intros binds body Hin.
  - destruct Hin.
  - simpl. destruct (Dyn.datacon_eq_dec K K') as [Heq|Hneq].
    + subst K'. eauto.
    + destruct Hin as [Hin | Hin].
      * inversion Hin; subst. congruence.
      * eapply IH. exact Hin.
Qed.

Lemma find_matching_pat_In : forall K pats p,
  Dyn.find_matching_pat K pats = Some p -> In p pats.
Proof.
  induction pats as [|[K' b' bd'] pats' IH]; intros; simpl in *.
  - discriminate.
  - destruct (Dyn.datacon_eq_dec K K') as [Heq|Hneq].
    + inversion H; subst. left; reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma ewf_to_field_starts : forall DI St r i Ts j,
  Dyn.end_witness_fields DI St r i Ts j ->
  exists indices, Dyn.field_starts DI St r i Ts indices.
Proof.
  intros. induction H.
  - exists nil. constructor.
  - destruct IHend_witness_fields as [idx Hfs].
    eexists (_ :: _). econstructor; eassumption.
Qed.

Lemma pats_have_type_In :
  forall FDs DI tc_s G S0 C pats p Al Nl A2 N2 t,
    Stat.pats_have_type FDs DI tc_s G S0 C Al Nl A2 N2 t pats ->
    In p pats ->
    exists A1 N1 A3 N3,
      Stat.pat_has_type FDs DI tc_s G S0 C A1 N1 A3 N3 t p.
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
    Stat.pat_has_type FDs DI tc_s G S0 C Al Nl A2 N2 t
                      (pat_clause dc binds body) ->
    exists tc fieldtcs,
      In (dc, (tc, fieldtcs)) DI /\ tc = tc_s /\
      pat_field_tycons binds = fieldtcs.
Proof.
  intros. inversion H; subst. eauto.
Qed.

(* ================================================================= *)
(* Lemma: Substitution  (thesis Appendix A, Lemma Substitution)       *)
(*                                                                    *)
(* Substituting well-typed values for variables in a well-typed       *)
(* expression preserves typing.  Simplified single-variable form.     *)
(* The full thesis version handles simultaneous value + location      *)
(* substitution.                                                      *)
(* ================================================================= *)

Lemma substitution_val :
  forall FDs DI Gamma x vty Sigma C A N A' N' e T v0,
    Stat.has_type FDs DI (cons (x, vty) Gamma) Sigma C A N A' N' e T ->
    Stat.has_type FDs DI Gamma Sigma C A N A N (e_val v0) vty ->
    Stat.has_type FDs DI Gamma Sigma C A N A' N' (Dyn.subst_val x v0 e) T.
Proof.
Admitted.

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
    Stat.has_type FDs DI G Sigma C A N A2 N2 e Tl ->
    G = @nil (term_var * ty) ->
    forall M St,
    store_wf DI Sigma C A N M St ->
    di_functional DI ->
    expr_wf M e ->
    (exists vl, e = e_val vl)
    \/ (exists St2 M2 e2, Dyn.step FDs DI St M e St2 M2 e2).
Proof.
  intros FDs DI G Sigma C A N A2 N2 e Tl Htype.
  induction Htype; intros HG M St Hwf Hdi Hewf; subst.

  (* ---- T_Var ----
     Γ = nil, so In (x, _) nil is False. *)
  1: { exfalso. simpl in H. exact H. }

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
    - subst. do 3 eexists. apply Dyn.D_Let_Val.
    - do 3 eexists. apply Dyn.D_Let_Expr.
      + destruct e1; try reflexivity. exfalso. inversion Hstep.
      + exact Hstep.
  }

  (* ---- T_LRegion ----
     Unconditionally steps with D_LetRegion. *)
  1: { right. do 3 eexists. apply Dyn.D_LetRegion. }

  (* ---- T_LLStart ----
     Unconditionally steps with D_LetLoc_Start. *)
  1: { right. do 3 eexists. apply Dyn.D_LetLoc_Start. }

  (* ---- T_LLTag ----
     From alloc_wf (write-once), (lprev,r) ∈ N gives
     M(lprev,r) = ⟨r,i⟩, so D_LetLoc_Tag applies. *)
  1: {
    right.
    destruct Hwf as [_ [_ [[_ [_ [Hwo _]]] _]]].
    destruct (Hwo lprev r H0) as [i [Hlk _]].
    do 3 eexists. eapply Dyn.D_LetLoc_Tag. exact Hlk.
  }

  (* ---- T_LLAfter ----
     From map-store consistency, ((l1,r),tc_prev) ∈ Σ gives
     M(l1,r) = ⟨r,i⟩ and end_witness, so D_LetLoc_After applies. *)
  1: {
    right.
    destruct Hwf as [Hms _].
    destruct (Hms l1 r tc_prev H0) as [i [j [Hlk Hew]]].
    do 3 eexists. eapply Dyn.D_LetLoc_After; eauto.
  }

  (* ---- T_DataCon ----
     From alloc_wf (write-once), (l,r) ∈ N gives
     M(l,r) = ⟨r,i⟩, so D_DataCon applies. *)
  1: {
    right.
    destruct Hwf as [_ [_ [[_ [_ [Hwo _]]] _]]].
    destruct (Hwo l r H0) as [i [Hlk _]].
    do 3 eexists. eapply Dyn.D_DataCon. exact Hlk.
  }

  (* ---- T_App ----
     The function declaration is in FDs (from T_App premise),
     so In_lookup_fdecl gives lookup success for D_App. *)
  1: {
    right.
    destruct (In_lookup_fdecl _ _ _ _ _ _ _ H)
      as [l' [p' [t' [rg' [b' Hlk]]]]].
    do 3 eexists. eapply Dyn.D_App. exact Hlk.
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
      match goal with [ Hin : In _ nil |- _ ] =>
        simpl in Hin; contradiction end.
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
      match goal with [ Hlookup : Dyn.lookup_datacon _ _ = Some _ |- _ ] =>
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
      match goal with [ Hewf : Dyn.end_witness_fields _ _ _ _ _ _ |- _ ] =>
        destruct (ewf_to_field_starts _ _ _ _ _ _ Hewf) as [indices Hfs]
      end.
      (* 9. Assemble D_Case *)
      do 3 eexists. eapply Dyn.D_Case; eauto.
  }

  (* Auxiliary goals from mutual induction (pat_has_type, pats_have_type).
     These are trivially satisfied since we only need progress for
     has_type, not for the pattern typing judgments. *)
  all: intros; left; eauto.
Qed.

Theorem progress :
  forall FDs DI Sigma C A N A' N' M S e T,
    Stat.has_type FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    di_functional DI ->
    expr_wf M e ->
    (exists v0, e = e_val v0)
    \/ (exists S' M' e', Dyn.step FDs DI S M e S' M' e').
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
    Stat.has_type FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    Dyn.step FDs DI S M e S' M' e' ->
    exists Sigma' C' A'' N'',
      Stat.has_type FDs DI nil Sigma' C' A' N' A'' N'' e' T
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
    Stat.has_type FDs DI nil Sigma C A N A' N' e T ->
    store_wf DI Sigma C A N M S ->
    di_functional DI ->
    expr_wf M e ->
    Dyn.multi_step FDs DI S M e Sn Mn en ->
    (exists v0, en = e_val v0)
    \/ (exists S' M' e', Dyn.step FDs DI Sn Mn en S' M' e').
Proof.
  (* By induction on multi_step:
     - MS_refl: apply progress.
     - MS_step: apply preservation to get new typing + store_wf,
                then apply IH. *)
Admitted.

End LoCalSafety.
