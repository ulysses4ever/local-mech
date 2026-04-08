(* LoCalDynamic.v — Dynamic (operational) semantics for LoCal.
   Implements the small-step transition relation from thesis §2.2.2,
   Figure 2.6.

   Configuration:  S ; M ; e  ⇒  S' ; M' ; e'
     S  = store       (region → heap of constructor tags)
     M  = location map (symbolic location → concrete address)
     e  = expression *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import PeanoNat.
From LocalMech Require Import LoCalSyntax.

Import LoCalSyntax.LoCalSyntax.

Module LoCalDynamic.

Open Scope string_scope.

(* ================================================================= *)
(* Runtime structures (Figure 2.5 of the thesis)                     *)
(* ================================================================= *)

(* Concrete address in the store: a region and an index. *)
Definition concrete_loc : Type := (region_var * nat)%type.

(* Heap: maps indices to data constructor tags within a region. *)
Definition heap : Type := list (nat * datacon).

(* Store: maps regions to heaps.
   S = {r₁ ↦ h₁, ..., rₙ ↦ hₙ} *)
Definition store : Type := list (region_var * heap).

(* Location map: maps symbolic locations to concrete addresses.
   M = {l₁^r₁ ↦ ⟨r₁,i₁⟩, ..., lₙ^rₙ ↦ ⟨rₙ,iₙ⟩} *)
Definition loc_map : Type := list (laddr * concrete_loc).

(* Runtime support carried by the location map.
   Named-mechanization refinement:
   the thesis's Freshen(FD) side condition for D_App needs to avoid the
   caller's live symbolic location support as well as the actual
   arguments.  We expose that support explicitly here so the dynamic rule
   can say what it is freshening against. *)
Definition loc_map_laddrs (M : loc_map) : list laddr :=
  List.map fst M.

Definition loc_map_regions (M : loc_map) : list region_var :=
  List.map snd (loc_map_laddrs M).

(* ================================================================= *)
(* Lookup operations                                                 *)
(* ================================================================= *)

(* M(l^r) — look up a symbolic location in the location map. *)
Fixpoint lookup_loc (M : loc_map) (addr : laddr) : option concrete_loc :=
  match M with
  | nil => None
  | (a, cl) :: M' => if laddr_eq_dec addr a then Some cl else lookup_loc M' addr
  end.

Fixpoint heap_find (h : heap) (i : nat) : option datacon :=
  match h with
  | nil => None
  | (j, K) :: h' => if Nat.eqb i j then Some K else heap_find h' i
  end.

Fixpoint store_find_heap (S : store) (r : region_var) : option heap :=
  match S with
  | nil => None
  | (r', h) :: S' =>
      if region_var_eq_dec r r' then Some h else store_find_heap S' r
  end.

(* S(r)(i) — look up the constructor tag at address i in region r. *)
Definition heap_lookup (S : store) (r : region_var) (i : nat) : option datacon :=
  match store_find_heap S r with
  | Some h => heap_find h i
  | None => None
  end.

(* ================================================================= *)
(* Update operations                                                 *)
(* ================================================================= *)

(* M ∪ {addr ↦ cl} *)
Definition extend_loc (M : loc_map) (addr : laddr) (cl : concrete_loc)
    : loc_map :=
  (addr, cl) :: M.

Definition heap_write (h : heap) (i : nat) (K : datacon) : heap :=
  (i, K) :: h.

(* S ∪ {r ↦ (i ↦ K)} — write tag K at address (r, i). *)
Fixpoint store_write (S : store) (r : region_var) (i : nat) (K : datacon)
    : store :=
  match S with
  | nil => [(r, [(i, K)])]
  | (r', h) :: S' =>
      if region_var_eq_dec r r' then (r', heap_write h i K) :: S'
      else (r', h) :: store_write S' r i K
  end.

(* ================================================================= *)
(* Value predicate                                                   *)
(* ================================================================= *)

Definition is_val (e : expr) : bool :=
  match e with
  | e_val _ => true
  | _ => false
  end.

(* ================================================================= *)
(* Term-variable substitution  (e[v/x])                              *)
(*                                                                    *)
(* This is the raw named-variable substitution on syntax.             *)
(* Capture avoidance is handled separately by explicit freshening,    *)
(* following the thesis's Freshen(...) side condition.                *)
(* ================================================================= *)

(* Substitute value s for term variable x in a value. *)
Definition subst_in_val (x : term_var) (s : val) (v0 : val) : val :=
  match v0 with
  | v_var y => if term_var_eq_dec x y then s else v0
  | v_cloc _ _ _ _ => v0
  end.

(* Substitute value s for term variable x in expressions/patterns. *)
Fixpoint subst_val (x : term_var) (s : val) (e : expr) {struct e} : expr :=
  match e with
  | e_val v0 => e_val (subst_in_val x s v0)
  | e_app f locs args =>
      e_app f locs (List.map (subst_in_val x s) args)
  | e_datacon K l r args =>
      e_datacon K l r (List.map (subst_in_val x s) args)
  | e_let y T e1 e2 =>
      e_let y T (subst_val x s e1)
                (if term_var_eq_dec x y then e2 else subst_val x s e2)
  | e_letloc l r le body =>
      e_letloc l r le (subst_val x s body)
  | e_letregion r body =>
      e_letregion r (subst_val x s body)
  | e_case v0 pats =>
      let fix go_pats (ps : list pat) : list pat :=
        match ps with
        | nil => nil
        | (pat_clause K binds body) :: ps' =>
            (if existsb
                  (fun b => if term_var_eq_dec x (fst b) then true else false)
                  binds
             then pat_clause K binds body
             else pat_clause K binds (subst_val x s body))
            :: go_pats ps'
        end
      in e_case (subst_in_val x s v0) (go_pats pats)
  end.

(* Multi-substitution: substitute values vs for variables xs. *)
Fixpoint subst_vals (xs : list term_var) (vs : list val) (e : expr) : expr :=
  match xs, vs with
  | x :: xs', v0 :: vs' => subst_vals xs' vs' (subst_val x v0 e)
  | _, _ => e
  end.

(* ================================================================= *)
(* Location/region substitution  (e[l_new^r_new / l_old^r_old])      *)
(*   Needed for D-App (location parameter instantiation).            *)
(* ================================================================= *)

Definition subst_lvar (old_l new_l : loc_var) (l : loc_var) : loc_var :=
  if loc_var_eq_dec old_l l then new_l else l.

Definition subst_rvar (old_r new_r : region_var) (r : region_var)
    : region_var :=
  if region_var_eq_dec old_r r then new_r else r.

Definition subst_loc_in_locexp
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (le : loc_exp) : loc_exp :=
  match le with
  | LE_Start r   => LE_Start (subst_rvar ro rn r)
  | LE_Next l r  =>
      LE_Next (if laddr_eq_dec (l, r) (lo, ro) then ln else l)
              (subst_rvar ro rn r)
  | LE_After T l r =>
      LE_After T
               (if laddr_eq_dec (l, r) (lo, ro) then ln else l)
               (subst_rvar ro rn r)
  end.

Definition subst_loc_in_ty
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (t : ty) : ty :=
  match t with
  | loc_ty T l r =>
      loc_ty T
             (if laddr_eq_dec (l, r) (lo, ro) then ln else l)
             (subst_rvar ro rn r)
  end.

Definition subst_loc_in_val
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (v0 : val) : val :=
  match v0 with
  | v_var _ => v0
  | v_cloc r i l rg =>
      v_cloc (subst_rvar ro rn r)
             i
             (if laddr_eq_dec (l, rg) (lo, ro) then ln else l)
             (subst_rvar ro rn rg)
  end.

Definition subst_loc_in_laddr
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (a : loc_var * region_var) : loc_var * region_var :=
  let '(l, r) := a in
  ((if laddr_eq_dec (l, r) (lo, ro) then ln else l),
   subst_rvar ro rn r).

Definition subst_loc_in_bind
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (b : term_var * ty) : term_var * ty :=
  (fst b, subst_loc_in_ty lo ro ln rn (snd b)).

(* Substitute location l_new^r_new for l_old^r_old throughout
   an expression. Uses nested fix for the list-of-patterns case. *)
Fixpoint subst_loc
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (e : expr) {struct e} : expr :=
  match e with
  | e_val v0 => e_val (subst_loc_in_val lo ro ln rn v0)
  | e_app f locs args =>
      e_app f (List.map (subst_loc_in_laddr lo ro ln rn) locs)
              (List.map (subst_loc_in_val lo ro ln rn) args)
  | e_datacon K l r args =>
      e_datacon K (subst_lvar lo ln l) (subst_rvar ro rn r)
                  (List.map (subst_loc_in_val lo ro ln rn) args)
  | e_let y T e1 e2 =>
      e_let y (subst_loc_in_ty lo ro ln rn T)
              (subst_loc lo ro ln rn e1)
              (subst_loc lo ro ln rn e2)
  | e_letloc l r le body =>
      e_letloc (subst_lvar lo ln l) (subst_rvar ro rn r)
               (subst_loc_in_locexp lo ro ln rn le)
               (subst_loc lo ro ln rn body)
  | e_letregion r body =>
      e_letregion (subst_rvar ro rn r) (subst_loc lo ro ln rn body)
  | e_case v0 pats =>
      let fix go_pats (ps : list pat) : list pat :=
        match ps with
        | nil => nil
        | (pat_clause K binds body) :: ps' =>
            pat_clause K
              (List.map (subst_loc_in_bind lo ro ln rn) binds)
              (subst_loc lo ro ln rn body)
            :: go_pats ps'
        end
      in e_case (subst_loc_in_val lo ro ln rn v0) (go_pats pats)
  end.

(* Multi-substitution: substitute actual location args for formal params. *)
Fixpoint subst_locs
    (formals actuals : list (loc_var * region_var))
    (e : expr) : expr :=
  match formals, actuals with
  | (lo, ro) :: fs, (ln, rn) :: as_ =>
      subst_locs fs as_ (subst_loc lo ro ln rn e)
  | _, _ => e
  end.

Definition subst_app_fresh_with_support
    (avoid_l : list laddr)
    (avoid_r : list region_var)
    (formals actuals : list (loc_var * region_var))
    (params : list (term_var * ty))
    (val_args : list val)
    (e : expr) : expr :=
  let e' :=
    freshen_expr_with
      (vals_term_vars val_args)
      (avoid_l ++ actuals ++ vals_symbolic_laddrs val_args)
      (avoid_r ++ loc_arg_regions actuals ++ vals_region_vars val_args)
      e in
  subst_locs formals actuals
    (subst_vals (List.map fst params) val_args e').

Definition subst_app_runtime_fresh
    (M : loc_map)
    (formals actuals : list (loc_var * region_var))
    (params : list (term_var * ty))
    (val_args : list val)
    (e : expr) : expr :=
  (* Dynamic-semantics refinement beyond the thesis prose:
     Freshen(FD) must avoid the caller's current symbolic runtime support,
     not only the actual arguments, or the named mechanization can
     collide with live entries already present in M. *)
  subst_app_fresh_with_support
    (loc_map_laddrs M)
    (loc_map_regions M)
    formals actuals params val_args e.

(* ================================================================= *)
(* End-witness relation  (thesis §2.2.2 and Appendix §end-witness)   *)
(*                                                                   *)
(*   ewitness(T, ⟨r, i_s⟩, S, ⟨r, i_e⟩)                              *)
(*                                                                   *)
(* Given type T and starting address (r, i_s) in store S, the        *)
(* serialized value of type T ends at address (r, i_e).              *)
(* ================================================================= *)

Inductive end_witness :
    datacon_info -> store -> concrete_loc -> tycon -> concrete_loc -> Prop :=
  (* The tag at i_s is constructor K of type tyc with fields fieldtys.
     The fields span from i_s+1 to j (computed by end_witness_fields). *)
  | EW_step : forall DI S r i_s K tyc fieldtys j,
      heap_lookup S r i_s = Some K ->
      lookup_datacon DI K = Some (tyc, fieldtys) ->
      end_witness_fields DI S r (i_s + 1) fieldtys j ->
      end_witness DI S (r, i_s) tyc (r, j)

with end_witness_fields :
    datacon_info -> store -> region_var -> nat -> list tycon -> nat -> Prop :=
  (* No fields remaining: the end is the current address. *)
  | EWF_nil : forall DI S r i,
      end_witness_fields DI S r i nil i
  (* One field of type T starts at i, ends at j;
     remaining fields start at j. *)
  | EWF_cons : forall DI S r i T Ts j k,
      end_witness DI S (r, i) T (r, j) ->
      end_witness_fields DI S r j Ts k ->
      end_witness_fields DI S r i (T :: Ts) k.

(* ================================================================= *)
(* Pattern matching helpers  (for D-Case)                            *)
(* ================================================================= *)

(* Find the pattern clause matching constructor K. *)
Fixpoint find_matching_pat (K : datacon) (pats : list pat)
    : option pat :=
  match pats with
  | nil => None
  | (pat_clause K' binds body) :: pats' =>
      if datacon_eq_dec K K' then Some (pat_clause K' binds body)
      else find_matching_pat K pats'
  end.

(* Compute field start addresses using end-witness chains.
   Given store S, region r, starting index i, and field types,
   produces the list of starting indices for each field.

   For types [T₁; T₂; T₃] starting at i:
     field 1 starts at i,      ends at w₁  (via end_witness on T₁)
     field 2 starts at w₁,     ends at w₂  (via end_witness on T₂)
     field 3 starts at w₂,     ends at w₃  (via end_witness on T₃)
   Result: [i; w₁; w₂] *)
Inductive field_starts :
    datacon_info -> store -> region_var -> nat ->
    list tycon -> list nat -> Prop :=
  | FS_nil : forall DI S r i,
      field_starts DI S r i nil nil
  | FS_cons : forall DI S r i T Ts j starts,
      end_witness DI S (r, i) T (r, j) ->
      field_starts DI S r j Ts starts ->
      field_starts DI S r i (T :: Ts) (i :: starts).

(* pat_field_tycons and pat_term_vars are imported from LoCalSyntax. *)

(* Build concrete-location values for pattern variable substitution.
   Each binding (x, T@l^r) at field start index i in region rc
   becomes value ⟨rc, i⟩^(l^r). *)
Fixpoint build_cloc_vals (rc : region_var)
    (binds : list (term_var * ty)) (indices : list nat) : list val :=
  match binds, indices with
  | bind :: binds', i :: indices' =>
      let '(l, r) := bind_laddr bind in
      v_cloc rc i l r :: build_cloc_vals rc binds' indices'
  | _, _ => nil
  end.

(* Extend location map with pattern field bindings.
   Each binding (_, T@l^r) at field start index i in region rc
   adds mapping (l,r) ↦ (rc, i). *)
Fixpoint extend_loc_fields (M : loc_map) (rc : region_var)
    (binds : list (term_var * ty)) (indices : list nat) : loc_map :=
  match binds, indices with
  | bind :: binds', i :: indices' =>
      extend_loc_fields (extend_loc M (bind_laddr bind) (rc, i))
                        rc binds' indices'
  | _, _ => M
  end.

(* ================================================================= *)
(* Step relation  (Figure 2.6 of the thesis)                         *)
(*                                                                   *)
(*   FDs ; DI ; S ; M ; e  ⇒  S' ; M' ; e'                           *)
(*     FDs = function declarations  (global context)                 *)
(*     DI  = datacon info           (global context)                 *)
(*     S   = store         M  = location map                         *)
(*     e   = expression                                              *)
(* ================================================================= *)

Inductive step :
    list fdecl -> datacon_info ->
    store -> loc_map -> expr ->
    store -> loc_map -> expr -> Prop :=

  (* ---- D-DataConstructor ----
     S; M; K l^r v₁...vₙ  ⇒  S'; M; ⟨r,i⟩^(l^r)
     where  ⟨r,i⟩ = M(l^r),   S' = S ∪ {r ↦ (i ↦ K)} *)
  | D_DataCon : forall FDs DI S M K l r vs rc i,
      lookup_loc M (l, r) = Some (rc, i) ->
      step FDs DI S M (e_datacon K l r vs)
           (store_write S rc i K) M (e_val (v_cloc rc i l r))

  (* ---- D-LetLoc-Start ----
     S; M; letloc l^r = start(r) in e  ⇒  S; M'; e
     where  M' = M ∪ {(l,r) ↦ ⟨r, 0⟩} *)
  | D_LetLoc_Start : forall FDs DI S M l r body,
      step FDs DI S M (e_letloc l r (LE_Start r) body)
           S (extend_loc M (l, r) (r, 0)) body

  (* ---- D-LetLoc-Tag ----
     S; M; letloc l^r = l'^r + 1 in e  ⇒  S; M'; e
     where  ⟨r,i⟩ = M(l'^r),   M' = M ∪ {(l,r) ↦ ⟨r, i+1⟩} *)
  | D_LetLoc_Tag : forall FDs DI S M l r l' body rc i,
      lookup_loc M (l', r) = Some (rc, i) ->
      step FDs DI S M (e_letloc l r (LE_Next l' r) body)
           S (extend_loc M (l, r) (rc, i + 1)) body

  (* ---- D-LetLoc-After ----
     S; M; letloc l^r = after(T@l₁^r) in e  ⇒  S; M'; e
     where  ⟨r,i⟩ = M(l₁^r),
            ewitness(T, ⟨r,i⟩, S, ⟨r,j⟩),
            M' = M ∪ {(l,r) ↦ ⟨r, j⟩} *)
  | D_LetLoc_After : forall FDs DI S M l r T l1 body rc i j,
      lookup_loc M (l1, r) = Some (rc, i) ->
      end_witness DI S (rc, i) T (rc, j) ->
      step FDs DI S M (e_letloc l r (LE_After T l1 r) body)
           S (extend_loc M (l, r) (rc, j)) body

  (* ---- D-Let-Expr ----
     S; M; e₁ ⇒ S'; M'; e₁'     e₁ ≠ v
     ─────────────────────────────────────────
     S; M; let x:τ = e₁ in e₂  ⇒  S'; M'; let x:τ = e₁' in e₂ *)
  | D_Let_Expr : forall FDs DI S M S' M' x T e1 e1' e2,
      is_val e1 = false ->
      step FDs DI S M e1 S' M' e1' ->
      step FDs DI S M (e_let x T e1 e2)
           S' M' (e_let x T e1' e2)

  (* ---- D-Let-Val ----
     S; M; let x:τ = v in e₂  ⇒  S; M; [v/x]e₂
     The thesis uses Freshen(FD) for function applications; the let
     rule itself is ordinary substitution. *)
  | D_Let_Val : forall FDs DI S M x T vl e2,
      step FDs DI S M (e_let x T (e_val vl) e2)
           S M (subst_val x vl e2)

  (* ---- D-LetRegion ----
     S; M; letregion r in e  ⇒  S; M; e *)
  | D_LetRegion : forall FDs DI S M r body,
      step FDs DI S M (e_letregion r body)
           S M body

  (* ---- D-App ----
     S; M; f [l₁^r₁,...] v₁...vₘ
       ⇒  S; M; e[x₁...xₘ := v₁...vₘ][l'₁^r'₁... := l₁^r₁...]
     where  FD = Function(f),
            (f x₁...xₘ = e) = Freshen(FD).

     Named-mechanization refinement:
     the freshened body must avoid the caller's current symbolic support
     from M as well as the actual arguments.  This makes explicit the
     Barendregt-style freshness side condition that is only implicit in
     the thesis text. *)
  | D_App : forall FDs DI S M f loc_args val_args
                   f_locs f_named_params f_retty f_regions f_body,
      lookup_fdecl FDs f =
        Some (FunDecl f f_locs f_named_params f_retty f_regions f_body) ->
      step FDs DI S M (e_app f loc_args val_args)
           S M (subst_app_runtime_fresh M f_locs loc_args f_named_params val_args f_body)

  (* ---- D-Case ----
     S; M; case ⟨r,i⟩^(l^r) of [..., K (x₁:τ₁@l₁^r,...) → e, ...]
       ⇒  S; M'; e[x₁ := ⟨r,w₁⟩^(l₁^r), ...]
     where  K = S(r)(i),
            field start addresses computed via end-witness chains,
            M' extends M with field location bindings *)
  | D_Case : forall FDs DI S M rc i l r pats
                    K binds body tyc fieldtys indices,
      (* Look up constructor tag at scrutinee address *)
      heap_lookup S rc i = Some K ->
      (* Find matching pattern branch *)
      find_matching_pat K pats = Some (pat_clause K binds body) ->
      (* Constructor's field types *)
      lookup_datacon DI K = Some (tyc, fieldtys) ->
      (* Pattern bindings are consistent with field types *)
      pat_field_tycons binds = fieldtys ->
      (* Compute field start addresses via end-witness chain *)
      field_starts DI S rc (i + 1) fieldtys indices ->
      (* Step: extend loc map, substitute concrete locs for pattern vars *)
      step FDs DI S M (e_case (v_cloc rc i l r) pats)
           S (extend_loc_fields M rc binds indices)
             (subst_vals (pat_term_vars binds)
                         (build_cloc_vals rc binds indices)
                         body).

(* ================================================================= *)
(* Multi-step relation (reflexive-transitive closure of step)        *)
(* ================================================================= *)

Inductive multi_step :
    list fdecl -> datacon_info ->
    store -> loc_map -> expr ->
    store -> loc_map -> expr -> Prop :=
  | MS_refl : forall FDs DI S M e,
      multi_step FDs DI S M e S M e
  | MS_step : forall FDs DI S M e S' M' e' S'' M'' e'',
      step FDs DI S M e S' M' e' ->
      multi_step FDs DI S' M' e' S'' M'' e'' ->
      multi_step FDs DI S M e S'' M'' e''.

(* ================================================================= *)
(* Example: Evaluation of tree allocation (thesis §2.2.2)            *)
(*                                                                   *)
(* The expression builds Node(Leaf, Leaf) in region r.               *)
(* Initial state:  S = {r ↦ ∅},  M = {l₀^r ↦ ⟨r, 0⟩}                 *)
(*                                                                   *)
(* Step 1  D-LetLoc-Tag:   bind l₁^r ↦ ⟨r, 1⟩                        *)
(* Step 2  D-Let-Expr/D-DataCon:  write Leaf at 1                    *)
(* Step 3  D-Let-Val:      substitute a := ⟨r,1⟩^(l₁^r)              *)
(* Step 4  D-LetLoc-After: bind l₂^r ↦ ⟨r, 2⟩  (end-witness Leaf)    *)
(* Step 5  D-Let-Expr/D-DataCon:  write Leaf at 2                    *)
(* Step 6  D-Let-Val:      substitute b := ⟨r,2⟩^(l₂^r)              *)
(* Step 7  D-DataCon:      write Node at 0  →  ⟨r,0⟩^(l₀^r)          *)
(*                                                                   *)
(* Final store: {r ↦ {0↦Node, 1↦Leaf, 2↦Leaf}}                       *)
(* ================================================================= *)

Section EvalExample.

Let l0 : loc_var    := "l_0".
Let l1 : loc_var    := "l_1".
Let l2 : loc_var    := "l_2".
Let r  : region_var := "r".
Let Tr : tycon      := "Tree".
Let Lf : datacon    := "Leaf".
Let Nd : datacon    := "Node".
Let a  : term_var   := "a".
Let b  : term_var   := "b".

Definition ex_DI : datacon_info :=
  [(Lf, (Tr, @nil tycon));
   (Nd, (Tr, [Tr; Tr]))].

Definition ex_tree_expr : expr :=
  LetLoc(l1, r, LE_Next l0 r,
    Let(a, loc_ty Tr l1 r, e_datacon Lf l1 r [],
      LetLoc(l2, r, LE_After Tr l1 r,
        Let(b, loc_ty Tr l2 r, e_datacon Lf l2 r [],
          e_datacon Nd l0 r [v_var a; v_var b])))).

Definition ex_S0 : store   := [(r, [])].
Definition ex_M0 : loc_map := [((l0, r), (r, 0))].

Example ex_eval_tree :
  multi_step nil ex_DI ex_S0 ex_M0 ex_tree_expr
             [(r, [(0, Nd); (2, Lf); (1, Lf)])]
             [((l2, r), (r, 2)); ((l1, r), (r, 1)); ((l0, r), (r, 0))]
             (e_val (v_cloc r 0 l0 r)).
Proof.
  unfold ex_tree_expr, ex_S0, ex_M0, ex_DI,
         l0, l1, l2, r, Tr, Lf, Nd, a, b.
  (* Step 1: D-LetLoc-Tag — bind l₁^r ↦ ⟨r, 1⟩ *)
  eapply MS_step. { apply D_LetLoc_Tag. reflexivity. }
  (* Step 2: D-Let-Expr + D-DataCon — write Leaf at address 1 *)
  eapply MS_step.
  { apply D_Let_Expr; [reflexivity | apply D_DataCon; reflexivity]. }
  (* Step 3: D-Let-Val — substitute a := ⟨r,1⟩^(l₁^r) *)
  eapply MS_step. { apply D_Let_Val. }
  cbn [subst_val
       fresh_term_var fresh_term_var_from fresh_loc_var fresh_loc_var_from
       fresh_region_var fresh_region_var_from term_var_with_ticks
       loc_var_with_ticks region_var_with_ticks tick_marks
       rename_term_in_expr rename_term_in_pat rename_term_in_val rename_term_in_bind
       rename_loc_in_expr rename_loc_in_pat rename_loc_in_val rename_loc_in_bind
       rename_loc_in_laddr rename_loc_in_locexp rename_loc_in_ty
       rename_region_in_expr rename_region_in_pat rename_region_in_val
       rename_region_in_bind rename_region_in_laddr rename_region_in_locexp
       rename_region_in_ty
       expr_occurs_term_vars pat_occurs_term_vars expr_occurs_loc_vars
       pat_occurs_loc_vars expr_occurs_region_vars pat_occurs_region_vars
       binds_loc_vars binds_region_vars val_loc_vars val_region_vars
       vals_loc_vars vals_region_vars loc_arg_loc_vars loc_arg_regions
       ty_loc_vars ty_region_vars locexp_loc_vars locexp_region_vars
       pat_term_vars pat_laddrs bind_loc_var bind_region_var
       subst_val subst_in_val List.map
       term_var_eq_dec string_dec Ascii.ascii_dec Bool.bool_dec
       existsb fst snd].
  (* Step 4: D-LetLoc-After — end-witness(Tree, ⟨r,1⟩, S, ⟨r,2⟩) *)
  eapply MS_step.
  { eapply D_LetLoc_After.
    - reflexivity.
    - eapply EW_step; [reflexivity | reflexivity | apply EWF_nil]. }
  (* Step 5: D-Let-Expr + D-DataCon — write Leaf at address 2 *)
  eapply MS_step.
  { apply D_Let_Expr; [reflexivity | apply D_DataCon; reflexivity]. }
  (* Step 6: D-Let-Val — substitute b := ⟨r,2⟩^(l₂^r) *)
  eapply MS_step. { apply D_Let_Val. }
  cbn [subst_val
       fresh_term_var fresh_term_var_from fresh_loc_var fresh_loc_var_from
       fresh_region_var fresh_region_var_from term_var_with_ticks
       loc_var_with_ticks region_var_with_ticks tick_marks
       rename_term_in_expr rename_term_in_pat rename_term_in_val rename_term_in_bind
       rename_loc_in_expr rename_loc_in_pat rename_loc_in_val rename_loc_in_bind
       rename_loc_in_laddr rename_loc_in_locexp rename_loc_in_ty
       rename_region_in_expr rename_region_in_pat rename_region_in_val
       rename_region_in_bind rename_region_in_laddr rename_region_in_locexp
       rename_region_in_ty
       expr_occurs_term_vars pat_occurs_term_vars expr_occurs_loc_vars
       pat_occurs_loc_vars expr_occurs_region_vars pat_occurs_region_vars
       binds_loc_vars binds_region_vars val_loc_vars val_region_vars
       vals_loc_vars vals_region_vars loc_arg_loc_vars loc_arg_regions
       ty_loc_vars ty_region_vars locexp_loc_vars locexp_region_vars
       pat_term_vars pat_laddrs bind_loc_var bind_region_var
       subst_val subst_in_val List.map
       term_var_eq_dec string_dec Ascii.ascii_dec Bool.bool_dec
       existsb fst snd].
  (* Step 7: D-DataCon — write Node at address 0 → final value *)
  eapply MS_step. { apply D_DataCon. reflexivity. }
  apply MS_refl.
Qed.

(* End-witness for the completed tree (thesis §2.2.2, paragraph after example):
   ewitness(Tree, ⟨r,0⟩, S_final, ⟨r,3⟩)
   Node at 0 has two Tree fields:
     Leaf at 1 → end at 2,  Leaf at 2 → end at 3. *)

Definition ex_S_final : store :=
  [(r, [(0, Nd); (2, Lf); (1, Lf)])].

Example ex_end_witness_tree :
  end_witness ex_DI ex_S_final (r, 0) Tr (r, 3).
Proof.
  unfold ex_DI, ex_S_final, r, Tr, Lf, Nd.
  eapply EW_step; [reflexivity | reflexivity |].
  (* Fields of Node: [Tree; Tree] starting at address 1 *)
  eapply EWF_cons.
  - (* Leaf at 1: no fields → end at 2 *)
    eapply EW_step; [reflexivity | reflexivity | apply EWF_nil].
  - eapply EWF_cons.
    + (* Leaf at 2: no fields → end at 3 *)
      eapply EW_step; [reflexivity | reflexivity | apply EWF_nil].
    + apply EWF_nil.
Qed.

End EvalExample.

End LoCalDynamic.
