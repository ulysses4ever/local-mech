Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Strings.String.
From LocalMech Require Import LoCalSyntax.
Module Import Syn := LoCalSyntax.LoCalSyntax.

Module LoCalStatic.

(* ================================================================= *)
(* Environment types and helpers for the LoCal type system (§2.2.1). *)
(* ================================================================= *)

(* Shorthand for the only type former. *)
Definition located_type : Type := ty.
Notation LocTy := loc_ty.
Notation ELet := e_let.

(* ---- Environments in the judgment  Γ; Σ; C; A; N ⊢ A'; N'; e : τ ---- *)

Definition type_env    : Type := list (term_var * located_type). (* Γ *)
Definition store_type  : Type := list (laddr * tycon).           (* Σ *)
Definition conloc_env  : Type := list (laddr * loc_exp).         (* C *)

Inductive alloc_ptr : Type :=
  | AP_None
  | AP_Loc : laddr -> alloc_ptr.

Definition alloc_env   : Type := list (region_var * alloc_ptr).  (* A *)
Definition nursery     : Type := list laddr.                     (* N *)

(* ---- Global contexts (not threaded through the judgment) ---- *)

(* Function environment: shared by typing and dynamics.
   Each entry is an fdecl (defined in LoCalSyntax). *)
Definition fun_env : Type := list fdecl.

(* ---- Environment operations ---- *)

Definition extend_tenv (G : type_env) (x : term_var) (t : located_type)
  : type_env := cons (x, t) G.

Definition extend_store (S0 : store_type) (lr : laddr) (tc : tycon)
  : store_type := cons (lr, tc) S0.

Definition extend_conloc (C0 : conloc_env) (lr : laddr) (le : loc_exp)
  : conloc_env := cons (lr, le) C0.

Definition extend_alloc (A0 : alloc_env) (r : region_var) (ap : alloc_ptr)
  : alloc_env := cons (r, ap) A0.

Definition extend_nursery (N0 : nursery) (lr : laddr) : nursery :=
  cons lr N0.

Definition remove_nursery (N0 : nursery) (lr : laddr) : nursery :=
  filter (fun x => if laddr_eq_dec x lr then false else true) N0.

(* Extend type_env with a list of bindings (for pattern branches). *)
Fixpoint extend_tenv_list (G : type_env) (binds : list (term_var * located_type))
  : type_env :=
  match binds with
  | nil => G
  | cons bnd rest => extend_tenv_list (cons bnd G) rest
  end.

(* Extract store-type entries from pattern bindings:
   (x, T@l^r) ↦ ((l,r), T). *)
Definition bind_to_store_entry (b : term_var * ty) : laddr * tycon :=
  match snd b with
  | loc_ty tc lv rv => ((lv, rv), tc)
  end.

Definition binds_to_store_entries (binds : list (term_var * ty))
  : list (laddr * tycon) :=
  map bind_to_store_entry binds.

Fixpoint extend_store_list (S0 : store_type) (entries : list (laddr * tycon))
  : store_type :=
  match entries with
  | nil => S0
  | cons ent rest => extend_store_list (cons ent S0) rest
  end.

(* Construct initial Γ and Σ from a parameter list (for T-FunctionDef). *)
Definition params_to_tenv (params : list (term_var * located_type))
  : type_env := params.

Definition params_to_store (params : list (term_var * located_type))
  : store_type := map bind_to_store_entry params.

(* Pattern coverage: every constructor of type tc in DI has a pattern. *)
Definition pats_cover (DI : datacon_info) (tc : tycon) (pats : list pat) : Prop :=
  forall K fts,
    In (K, (tc, fts)) DI ->
    exists binds body, In (pat_clause K binds body) pats.

(* ================================================================= *)
(* Typing judgments for LoCal (thesis §2.2.1, Figures types1/types2) *)
(*                                                                   *)
(* Judgment: FDs; DI; Γ; Σ; C; A; N ⊢ A'; N'; e : τ                *)
(*   FDs, DI are global contexts (fun declarations, datacon info).  *)
(* ================================================================= *)

Inductive has_type :
  fun_env ->
  datacon_info ->
  (* input environments *)
  type_env ->      (* Γ *)
  store_type ->    (* Σ *)
  conloc_env ->    (* C *)
  alloc_env ->     (* A  — input *)
  nursery ->       (* N  — input *)
  (* output environments *)
  alloc_env ->     (* A' — output *)
  nursery ->       (* N' — output *)
  (* expression and its type *)
  expr ->
  located_type ->
  Prop :=

  (* ---- T-Var (thesis: \tvar) ----
     Γ(x) = τ@l^r    Σ((l,r)) = τ
     ——————————————————————————————————
     Γ;Σ;C;A;N ⊢ A;N; x : τ@l^r       *)
  | T_Var :
      forall FDs DI G S0 C A N x tc l r,
        In (x, LocTy tc l r) G ->
        In ((l, r), tc) S0 ->
        has_type FDs DI G S0 C A N A N (e_val (v_var x)) (LocTy tc l r)

  (* ---- T-ConcreteLoc (thesis: \tconcreteloc) ----
     Σ((l,r)) = τ
     ————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A;N; concreteloc(r0,i,l^r) : τ@l^r *)
  | T_ConcreteLoc :
      forall FDs DI G S0 C A N r0 i l r tc,
        In ((l, r), tc) S0 ->
        has_type FDs DI G S0 C A N A N
                 (e_val (v_cloc r0 i l r)) (LocTy tc l r)

  (* ---- T-Let (thesis: \tlet) ----
     Γ;Σ;C;A;N ⊢ A';N'; e1 : τ1@l1^r1
     Γ';Σ';C;A';N' ⊢ A'';N''; e2 : τ2@l2^r2
     where Γ' = Γ ∪ {x ↦ τ1@l1^r1},  Σ' = Σ ∪ {(l1,r1) ↦ τ1}
     ———————————————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A'';N''; let x:τ1@l1^r1 = e1 in e2 : τ2@l2^r2 *)
  | T_Let :
      forall FDs DI G S0 C A N A' N' A'' N''
             x e1 e2 tc1 l1 r1 tc2 l2 r2,
        has_type FDs DI G S0 C A N A' N' e1 (LocTy tc1 l1 r1) ->
        has_type FDs DI (extend_tenv G x (LocTy tc1 l1 r1))
                       (extend_store S0 (l1, r1) tc1)
                       C A' N' A'' N'' e2 (LocTy tc2 l2 r2) ->
        has_type FDs DI G S0 C A N A'' N''
                 (ELet x (LocTy tc1 l1 r1) e1 e2) (LocTy tc2 l2 r2)

  (* ---- T-LetRegion (thesis: \tlregion) ----
     Γ;Σ;C;A';N ⊢ A'';N'; e : τ    where A' = A ∪ {r ↦ ∅}
     ——————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A'';N'; letregion r in e : τ *)
  | T_LRegion :
      forall FDs DI G S0 C A N A' N' r e t,
        has_type FDs DI G S0 C (extend_alloc A r AP_None) N A' N' e t ->
        has_type FDs DI G S0 C A N A' N' (e_letregion r e) t

  (* ---- T-LLStart (thesis: \tllstart) ----
     A(r) = ∅    (l,r) ∉ N''    (l',r') ≠ (l,r)
     Γ;Σ;C';A';N' ⊢ A'';N''; e : τ'@l'^r'
     where C' = C ∪ {(l,r) ↦ start(r)},
           A' = A ∪ {r ↦ (l,r)},  N' = N ∪ {(l,r)}
     ——————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A'';N''; letloc l^r = start(r) in e : τ'@l'^r' *)
  | T_LLStart :
      forall FDs DI G S0 C A N A'' N'' l r e tc' l' r',
        In (r, AP_None) A ->
        ~ In (l, r) N'' ->
        (l', r') <> (l, r) ->
        has_type FDs DI G S0
                 (extend_conloc C (l, r) (LE_Start r))
                 (extend_alloc A r (AP_Loc (l, r)))
                 (extend_nursery N (l, r))
                 A'' N'' e (LocTy tc' l' r') ->
        has_type FDs DI G S0 C A N A'' N''
                 (e_letloc l r (LE_Start r) e) (LocTy tc' l' r')

  (* ---- T-LLTag (thesis: \tlltag) ----
     A(r) = (lprev,r)    (lprev,r) ∈ N    (l,r) ∉ N''
     (l,r) ≠ (l'',r'')
     Γ;Σ;C';A';N' ⊢ A'';N''; e : τ''@l''^r''
     where C' = C ∪ {(l,r) ↦ (lprev,r)+1},
           A' = A ∪ {r ↦ (l,r)},  N' = N ∪ {(l,r)}
     ——————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A'';N''; letloc l^r = lprev^r+1 in e : τ''@l''^r'' *)
  | T_LLTag :
      forall FDs DI G S0 C A N A'' N'' l lprev r e tc'' l'' r'',
        In (r, AP_Loc (lprev, r)) A ->
        In (lprev, r) N ->
        ~ In (l, r) N'' ->
        (l, r) <> (l'', r'') ->
        has_type FDs DI G S0
                 (extend_conloc C (l, r) (LE_Next lprev r))
                 (extend_alloc A r (AP_Loc (l, r)))
                 (extend_nursery N (l, r))
                 A'' N'' e (LocTy tc'' l'' r'') ->
        has_type FDs DI G S0 C A N A'' N''
                 (e_letloc l r (LE_Next lprev r) e) (LocTy tc'' l'' r'')

  (* ---- T-LLAfter (thesis: \tllafter) ----
     A(r) = (l1,r)    Σ((l1,r)) = τ_prev    (l1,r) ∉ N
     (l,r) ∉ N''    (l,r) ≠ (l',r')
     Γ;Σ;C';A';N' ⊢ A'';N''; e : τ'@l'^r'
     where C' = C ∪ {(l,r) ↦ after(τ_prev,l1,r)},
           A' = A ∪ {r ↦ (l,r)},  N' = N ∪ {(l,r)}
     ——————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A'';N''; letloc l^r = after(τ_prev,l1,r) in e : τ'@l'^r' *)
  | T_LLAfter :
      forall FDs DI G S0 C A N A'' N'' l l1 r tc_prev e tc' l' r',
        In (r, AP_Loc (l1, r)) A ->
        In ((l1, r), tc_prev) S0 ->
        ~ In (l1, r) N ->
        ~ In (l, r) N'' ->
        (l, r) <> (l', r') ->
        has_type FDs DI G S0
                 (extend_conloc C (l, r) (LE_After tc_prev l1 r))
                 (extend_alloc A r (AP_Loc (l, r)))
                 (extend_nursery N (l, r))
                 A'' N'' e (LocTy tc' l' r') ->
        has_type FDs DI G S0 C A N A'' N''
                 (e_letloc l r (LE_After tc_prev l1 r) e) (LocTy tc' l' r')

  (* ---- T-DataCon (thesis: \tdatacon) ----
     typeofcon(dc) = tc    fieldtypes(dc) = [ft_1,...,ft_n]
     (l,r) ∈ N    n = |vs|
     Γ;Σ;C;A;N ⊢ A;N; v_i : ft_i@l_i^r  (for each i)
     [+ alloc-pointer & conloc chain premises — see thesis]
     ————————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A';N'; dc(l^r, vs) : tc@l^r
     where A' = A ∪ {r ↦ (l,r)},  N' = N − {(l,r)} *)
  | T_DataCon :
      forall FDs DI G S0 C A N (dc : datacon) (l : loc_var) (r : region_var)
             (vs : list val) (tc : tycon) (fieldtcs : list tycon),
        In (dc, (tc, fieldtcs)) DI ->
        In (l, r) N ->
        List.length vs = List.length fieldtcs ->
        (* TODO: alloc-pointer chain, conloc chain,
           and individual field value typing premises *)
        has_type FDs DI G S0 C A N
                 (extend_alloc A r (AP_Loc (l, r)))
                 (remove_nursery N (l, r))
                 (e_datacon dc l r vs) (LocTy tc l r)

  (* ---- T-App (thesis: \tapp) ----
     f : ∀[l''^r'']. (τ_i@l'''_i^r'''_i) → τ@l'''^r'''
     |lrs| = |sig_locs|    |vs| = |sig_args|
     (l,r) ∈ N    A(r) = (l,r)
     Γ;Σ;C;A;N ⊢ A;N; v_i : τ_i'  (for each i)
     [+ location-instantiation correspondence — see thesis]
     ————————————————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A;N'; f [lrs] vs : τ@l^r
     where N' = N − {(l,r)} *)
  | T_App :
      forall FDs DI G S0 C A N (f : fun_var)
             (lrs : list (loc_var * region_var)) (vs : list val)
             (tc : tycon) (l : loc_var) (r : region_var)
             f_locs f_params f_retty f_regions f_body,
        In (FunDecl f f_locs f_params f_retty f_regions f_body) FDs ->
        In (l, r) N ->
        In (r, AP_Loc (l, r)) A ->
        List.length lrs = List.length f_locs ->
        List.length vs = List.length f_params ->
        (* TODO: location-instantiation correspondence,
           individual value typing *)
        has_type FDs DI G S0 C A N
                 A (remove_nursery N (l, r))
                 (e_app f lrs vs) (LocTy tc l r)

  (* ---- T-Case (thesis: \tcase) ----
     Γ;Σ;C;A;N ⊢ A;N; v : τ_s@l_s^r_s
     τ_s; Γ;Σ;C;A;N ⊢_pat A';N'; pats : τ
     ————————————————————————————————————————
     Γ;Σ;C;A;N ⊢ A';N'; case v of pats : τ *)
  | T_Case :
      forall FDs DI G S0 C A N A' N' scrut ps tc_s l_s r_s t,
        has_type FDs DI G S0 C A N A N
                 (e_val scrut) (LocTy tc_s l_s r_s) ->
        pats_cover DI tc_s ps ->
        pats_have_type FDs DI tc_s G S0 C A N A' N' t ps ->
        has_type FDs DI G S0 C A N A' N' (e_case scrut ps) t

(* Pattern judgment:  τ_s; Γ; Σ; C; A; N ⊢_pat A'; N'; pat : τ
   τ_s is the scrutinee's type constructor. *)
with pat_has_type :
  fun_env -> datacon_info ->
  tycon ->       (* scrutinee type constructor *)
  type_env -> store_type -> conloc_env ->
  alloc_env -> nursery ->
  alloc_env -> nursery ->
  located_type -> pat -> Prop :=

  (* ---- T-Pat (thesis: \tpat) ----
     typeofcon(dc) = τ_s    fieldtypes(dc) = [ft_1,...,ft_n]
     Σ((l,r)) = τ_res
     (l,r) ≠ (l'_i, r'_i) for each binding location
     Γ';Σ';C;A;N ⊢ A';N'; body : τ_res@l^r
     where Γ' = Γ ∪ {x_i ↦ ft_i@l'_i^r'_i},
           Σ' = Σ ∪ {(l'_i,r'_i) ↦ ft_i} *)
  | T_Pat :
      forall FDs DI tc_s G S0 C A N A' N'
             dc binds body tc fieldtcs tc_res l r,
        In (dc, (tc, fieldtcs)) DI ->
        tc = tc_s ->
        pat_field_tycons binds = fieldtcs ->
        In ((l, r), tc_res) S0 ->
        has_type FDs DI
                 (extend_tenv_list G binds)
                 (extend_store_list S0 (binds_to_store_entries binds))
                 C A N A' N' body (LocTy tc_res l r) ->
        pat_has_type FDs DI tc_s G S0 C A N A' N'
                     (LocTy tc_res l r) (pat_clause dc binds body)

with pats_have_type :
  fun_env -> datacon_info ->
  tycon ->
  type_env -> store_type -> conloc_env ->
  alloc_env -> nursery ->
  alloc_env -> nursery ->
  located_type -> list pat -> Prop :=

  | T_PatsNil :
      forall FDs DI tc_s G S0 C A N t,
        pats_have_type FDs DI tc_s G S0 C A N A N t nil

  | T_PatsCons :
      forall FDs DI tc_s G S0 C A N A1 N1 A2 N2 t p ps,
        pat_has_type FDs DI tc_s G S0 C A N A1 N1 t p ->
        pats_have_type FDs DI tc_s G S0 C A1 N1 A2 N2 t ps ->
        pats_have_type FDs DI tc_s G S0 C A N A2 N2 t (cons p ps).

(* ---- T-FunctionDef (thesis: \tfunctiondef) ----
   Γ;Σ;C;A;N ⊢ A;N'; body : τ@l^r    (l,r) ∉ N'
   where Γ = {x_i ↦ arg_i}, Σ = {(l_i,r_i) ↦ tc_i} from args,
         C = ∅,  A = {r_out ↦ (l_out,r_out)},  N = {(l_out,r_out)}
   [+ location-param correspondence — see thesis] *)
Inductive fdecl_has_type : fun_env -> datacon_info -> fdecl -> Prop :=
  | T_FunctionDef :
      forall FDs DI f locs (named_args : list (term_var * ty)) out regions body
             N' tc_out l_out r_out,
        In (FunDecl f locs named_args out regions body) FDs ->
        out = LocTy tc_out l_out r_out ->
        (* Build initial environments from parameters. *)
        has_type FDs DI
                 named_args
                 (params_to_store named_args)
                 nil  (* C = ∅ *)
                 (cons (r_out, AP_Loc (l_out, r_out)) nil)
                 (cons (l_out, r_out) nil)
                 (cons (r_out, AP_Loc (l_out, r_out)) nil)
                 N'
                 body out ->
        ~ In (l_out, r_out) N' ->
        fdecl_has_type FDs DI (FunDecl f locs named_args out regions body).

(* ---- T-Program (thesis: \tprogram) ----
   ⊢_fun FD_i  (for each function declaration)
   Γ;Σ;C;A;N ⊢ A';N'; main : τ@l^r
   where Γ = ∅, Σ = ∅,
         C = {(l,r) ↦ start(r)},
         A = {r ↦ (l,r)},
         N = {(l,r)} *)
Inductive program_has_type : fun_env -> datacon_info -> program -> Prop :=
  | T_Program :
      forall FDs DI dds fds main A' N' tc l r,
        Forall (fdecl_has_type FDs DI) fds ->
        has_type FDs DI
                 nil
                 nil
                 (cons ((l, r), LE_Start r) nil)
                 (cons (r, AP_Loc (l, r)) nil)
                 (cons (l, r) nil)
                 A' N' main (LocTy tc l r) ->
        program_has_type FDs DI (Program dds fds main).

(* ================================================================= *)
(* Example: Typing derivation for the thesis §2.2.1 table.          *)
(*                                                                   *)
(* The table tracks A, C, N through an expression that builds a      *)
(* binary tree (Node with two Leaf children).  The first line        *)
(* "letloc l^r = start(r)" represents the function-context setup    *)
(* via T-FunctionDef, so our expression starts from line 2.          *)
(*   Initial envs:  Γ = Σ = C = ∅,  A = {r ↦ (l,r)},  N = {(l,r)} *)
(* ================================================================= *)

Section TypingExample.

Let l  : loc_var    := "l".
Let la : loc_var    := "l_a".
Let lb : loc_var    := "l_b".
Let r  : region_var := "r".
Let T  : tycon      := "T".
Let Lf : datacon    := "Leaf".
Let Nd : datacon    := "Node".
Let x  : term_var   := "x".
Let y  : term_var   := "y".

(* Datacon info: Leaf() → T,   Node(T, T) → T. *)
Definition ex_DI : datacon_info :=
  [(Lf, (T, @nil tycon));
   (Nd, (T, [T; T]))].

(* The expression (lines 2–6 of the thesis table). *)
Definition ex_build_tree : expr :=
  LetLoc(la, r, LE_Next l r,
    Let(x, loc_ty T la r, e_datacon Lf la r [],
      LetLoc(lb, r, LE_After T la r,
        Let(y, loc_ty T lb r, e_datacon Lf lb r [],
          e_datacon Nd l r [v_var x; v_var y])))).

(* Initial environments from function context (line 1 of the table). *)
Definition ex_A0 : alloc_env := [(r, AP_Loc (l, r))].
Definition ex_N0 : nursery   := [(l, r)].

Example ex_step_by_step_typing : exists A' N',
  has_type nil ex_DI nil nil nil ex_A0 ex_N0 A' N'
           ex_build_tree (loc_ty T l r).
Proof.
  eexists; eexists.
  unfold ex_build_tree, ex_A0, ex_N0, ex_DI,
         l, la, lb, r, T, Lf, Nd, x, y.
  (* Line 2: letloc l_a^r = l^r + 1 — T_LLTag *)
  eapply T_LLTag;
    [ left; reflexivity        (* A(r) = (l,r) *)
    | left; reflexivity        (* (l,r) ∈ N *)
    | shelve                   (* (l_a,r) ∉ N'' — deferred *)
    | intro H; congruence      (* (l,r) ≠ (l_a,r) *)
    | idtac ].
  (* Line 3: let x : T@l_a^r = Leaf(l_a^r) — T_Let *)
  eapply T_Let.
  - (* Leaf l_a^r [] — T_DataCon *)
    eapply T_DataCon;
      [ left; reflexivity      (* Leaf ∈ DI *)
      | left; reflexivity      (* (l_a,r) ∈ N *)
      | reflexivity ].         (* |[]| = |[]| *)
  - (* Line 4: letloc l_b^r = after(T@l_a^r) — T_LLAfter *)
    eapply T_LLAfter;
      [ left; reflexivity      (* A(r) = (l_a,r) *)
      | left; reflexivity      (* Σ((l_a,r)) = T *)
      | cbn; intros [H|[]]; congruence (* (l_a,r) ∉ [(l,r)] *)
      | shelve                 (* (l_b,r) ∉ N'' — deferred *)
      | intro H; congruence    (* (l,r) ≠ (l_b,r) *)
      | idtac ].
    (* Line 5: let y : T@l_b^r = Leaf(l_b^r) — T_Let *)
    eapply T_Let.
    + (* Leaf l_b^r [] — T_DataCon *)
      eapply T_DataCon;
        [ left; reflexivity    (* Leaf ∈ DI *)
        | left; reflexivity    (* (l_b,r) ∈ N *)
        | reflexivity ].       (* |[]| = |[]| *)
    + (* Line 6: Node l^r [x, y] — T_DataCon *)
      eapply T_DataCon;
        [ right; left; reflexivity  (* Node ∈ DI *)
        | cbn; left; reflexivity    (* (l,r) ∈ N *)
        | reflexivity ].            (* |[x,y]| = |[T,T]| *)
  (* Resolve deferred nursery-freshness goals:
     Both output nurseries are nil after all allocations. *)
  Unshelve.
  all: cbn; tauto.
Qed.

End TypingExample.

End LoCalStatic.
