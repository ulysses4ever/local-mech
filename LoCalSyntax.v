Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module LoCalSyntax.

(* Distinct identifier spaces to avoid mixing unrelated strings. *)
Inductive tycon : Type := mk_tycon : string -> tycon.
Inductive datacon : Type := mk_datacon : string -> datacon.
Inductive fun_var : Type := mk_fun_var : string -> fun_var.
Inductive term_var : Type := mk_term_var : string -> term_var.
Inductive loc_var : Type := mk_loc_var : string -> loc_var.
Inductive region_var : Type := mk_region_var : string -> region_var.

Coercion mk_tycon : string >-> tycon.
Coercion mk_datacon : string >-> datacon.
Coercion mk_fun_var : string >-> fun_var.
Coercion mk_term_var : string >-> term_var.
Coercion mk_loc_var : string >-> loc_var.
Coercion mk_region_var : string >-> region_var.

Inductive loc_exp : Type :=
  | LE_Start : region_var -> loc_exp
  | LE_Next : loc_var -> region_var -> loc_exp
  | LE_After : tycon -> loc_var -> region_var -> loc_exp.

Inductive ty : Type :=
  | loc_ty : tycon -> loc_var -> region_var -> ty.

Inductive val : Type :=
  | v_var : term_var -> val
  | v_cloc : region_var -> nat -> loc_var -> region_var -> val.

Inductive pat : Type :=
  | pat_clause : datacon -> list (term_var * ty) -> expr -> pat
with expr : Type :=
  | e_val : val -> expr
  | e_app : fun_var -> list (loc_var * region_var) -> list val -> expr
  | e_datacon : datacon -> loc_var -> region_var -> list val -> expr
  | e_let : term_var -> ty -> expr -> expr -> expr
  | e_letloc : loc_var -> region_var -> loc_exp -> expr -> expr
  | e_letregion : region_var -> expr -> expr
  | e_case : val -> list pat -> expr.

Inductive datatype_decl : Type :=
  | DataDecl : tycon -> list (datacon * list tycon) -> datatype_decl.

Inductive fdecl : Type :=
  | FunDecl : fun_var
              -> list (loc_var * region_var)   (* location params  *)
              -> list (term_var * ty)          (* named value params *)
              -> ty                            (* return type *)
              -> list region_var               (* region params *)
              -> expr                          (* body *)
              -> fdecl.

Record program : Type := Program
  { prog_ddecls : list datatype_decl;
    prog_fdecls : list fdecl;
    prog_main : expr }.

(* ================================================================= *)
(* Decidable equality for all identifier types                        *)
(* ================================================================= *)

Lemma datacon_eq_dec : forall (a b : datacon), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Lemma fun_var_eq_dec : forall (a b : fun_var), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Lemma term_var_eq_dec : forall (a b : term_var), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Lemma loc_var_eq_dec : forall (a b : loc_var), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Lemma region_var_eq_dec : forall (a b : region_var), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

(* Symbolic location address: a (loc_var, region_var) pair. *)
Definition laddr : Type := (loc_var * region_var)%type.

Lemma laddr_eq_dec : forall (a b : laddr), {a = b} + {a <> b}.
Proof. decide equality; [apply region_var_eq_dec | apply loc_var_eq_dec]. Defined.

(* Datacon info: maps constructor names to (result tycon, field tycons). *)
Definition datacon_info : Type := list (datacon * (tycon * list tycon)).

(* Shared finite-map lookups for the global LoCal contexts.
   These are used by both the typing and dynamic developments, so they
   live in the common syntax/context layer rather than in LoCalDynamic. *)

Fixpoint lookup_datacon (DI : datacon_info) (K : datacon)
    : option (tycon * list tycon) :=
  match DI with
  | nil => None
  | (K', info) :: DI' =>
      if datacon_eq_dec K K' then Some info else lookup_datacon DI' K
  end.

Fixpoint lookup_fdecl (FDs : list fdecl) (f : fun_var) : option fdecl :=
  match FDs with
  | nil => None
  | fd :: FDs' =>
      match fd with
      | FunDecl f' _ _ _ _ _ =>
          if fun_var_eq_dec f f' then Some fd else lookup_fdecl FDs' f
      end
  end.

(* Shared location/region substitution on syntax-level objects.
   These are used both by static instantiation and by the dynamic
   semantics of function application. *)

Definition subst_lvar (old_l new_l : loc_var) (l : loc_var) : loc_var :=
  if loc_var_eq_dec old_l l then new_l else l.

Definition subst_rvar (old_r new_r : region_var) (r : region_var)
    : region_var :=
  if region_var_eq_dec old_r r then new_r else r.

Definition subst_loc_in_laddr
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (a : laddr) : laddr :=
  let '(l, r) := a in
  ((if laddr_eq_dec (l, r) (lo, ro) then ln else l),
   subst_rvar ro rn r).

Definition subst_loc_in_locexp
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (le : loc_exp) : loc_exp :=
  match le with
  | LE_Start r => LE_Start (subst_rvar ro rn r)
  | LE_Next l r =>
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

Definition subst_loc_in_bind
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (b : term_var * ty) : term_var * ty :=
  (fst b, subst_loc_in_ty lo ro ln rn (snd b)).

Fixpoint subst_locs_in_ty
    (formals actuals : list laddr) (t : ty) : ty :=
  match formals, actuals with
  | (lo, ro) :: fs, (ln, rn) :: as_ =>
      subst_locs_in_ty fs as_ (subst_loc_in_ty lo ro ln rn t)
  | _, _ => t
  end.

Declare Custom Entry local_ty.
Declare Custom Entry local_val.
Declare Custom Entry local_exp.
Declare Scope local_scope.

Notation "<{{ t }}>" := t (t custom local_ty at level 200).
Notation "<{ e }>" := e (e custom local_exp at level 200).

Notation "'at' T '@' l '^' r" :=
  (loc_ty T l r)
    (in custom local_ty at level 80, T constr, l constr, r constr)
    : local_scope.

Notation "'v' x" := (v_var x)
  (in custom local_val at level 10, x constr) : local_scope.

Notation "'cloc' '(' r ',' i ',' l '^' rg ')'" := (v_cloc r i l rg)
  (in custom local_val at level 10, r constr, i constr, l constr, rg constr)
  : local_scope.

Notation "'start' r" := (LE_Start r)
  (in custom local_exp at level 10, r constr) : local_scope.

Notation "'case' scrut 'of' branches" :=
  (e_case scrut branches)
    (in custom local_exp at level 80, scrut constr, branches constr)
    : local_scope.

(* Parse-safe aliases for let/letloc (infix forms conflict with this grammar). *)
Notation "'LetLoc(' l ',' r ',' le ',' e ')'" := (e_letloc l r le e)
  (at level 0, l constr, r constr, le at level 200, e at level 200) : local_scope.

Notation "'Let(' x ',' T ',' e1 ',' e2 ')'" := (e_let x T e1 e2)
  (at level 0, x constr, T at level 200, e1 at level 200, e2 at level 200) : local_scope.

Open Scope local_scope.

Definition ex_tree_alloc : expr :=
  LetLoc("l", "r", <{ start "r" }>,
    LetLoc("l_a", "r", LE_Next "l" "r",
      Let("x", loc_ty "Tree" "l_a" "r", e_datacon "Leaf" "l_a" "r" [],
        LetLoc("l_b", "r", LE_After "Tree" "l_a" "r",
          Let("y", loc_ty "Tree" "l_b" "r", e_datacon "Leaf" "l_b" "r" [],
            e_datacon "Node" "l" "r" [v_var "x"; v_var "y"]))))).

Definition ex_tree_case : expr :=
  Let("t1", loc_ty "Tree" "l_t" "r", e_val (v_var "t"),
    <{ case (v_var "t1") of
         [ pat_clause "Leaf"
             [(mk_term_var "n", loc_ty "Int" "l_n" "r")]
             (e_val (v_var "n"));
           pat_clause "Node"
             [(mk_term_var "x", loc_ty "Tree" "l_x" "r");
              (mk_term_var "y", loc_ty "Tree" "l_y" "r")]
             (e_val (v_var "x")) ] }>).

(* Helpers on pattern bindings — used by both typing and dynamic rules. *)

Definition bind_tycon (b : term_var * ty) : tycon :=
  match snd b with
  | loc_ty T _ _ => T
  end.

Definition bind_laddr (b : term_var * ty) : laddr :=
  match snd b with
  | loc_ty _ l r => (l, r)
  end.

Definition bind_store_entry (b : term_var * ty) : laddr * tycon :=
  (bind_laddr b, bind_tycon b).

Definition pat_field_tycons (binds : list (term_var * ty)) : list tycon :=
  List.map bind_tycon binds.

Definition pat_term_vars (binds : list (term_var * ty)) : list term_var :=
  List.map fst binds.

Definition pat_laddrs (binds : list (term_var * ty)) : list laddr :=
  List.map bind_laddr binds.

Definition pat_store_entries (binds : list (term_var * ty))
    : list (laddr * tycon) :=
  List.map bind_store_entry binds.

Definition bind_loc_var (b : term_var * ty) : loc_var :=
  fst (bind_laddr b).

Definition bind_region_var (b : term_var * ty) : region_var :=
  snd (bind_laddr b).

Definition val_term_vars (v0 : val) : list term_var :=
  match v0 with
  | v_var x => [x]
  | v_cloc _ _ _ _ => nil
  end.

Definition val_loc_vars (v0 : val) : list loc_var :=
  match v0 with
  | v_var _ => nil
  | v_cloc _ _ l _ => [l]
  end.

Definition val_symbolic_laddrs (v0 : val) : list laddr :=
  match v0 with
  | v_var _ => nil
  | v_cloc _ _ l r => [(l, r)]
  end.

Definition val_region_vars (v0 : val) : list region_var :=
  match v0 with
  | v_var _ => nil
  | v_cloc rc _ _ rg => [rc; rg]
  end.

Definition vals_term_vars (vs : list val) : list term_var :=
  flat_map val_term_vars vs.

Definition vals_loc_vars (vs : list val) : list loc_var :=
  flat_map val_loc_vars vs.

Definition vals_symbolic_laddrs (vs : list val) : list laddr :=
  flat_map val_symbolic_laddrs vs.

Definition vals_region_vars (vs : list val) : list region_var :=
  flat_map val_region_vars vs.

Definition loc_arg_loc_vars (loc_args : list laddr) : list loc_var :=
  List.map fst loc_args.

Definition loc_arg_regions (loc_args : list laddr) : list region_var :=
  List.map snd loc_args.

Fixpoint pat_bound_term_vars (p : pat) : list term_var :=
  match p with
  | pat_clause _ binds body => pat_term_vars binds ++ expr_bound_term_vars body
  end

with expr_bound_term_vars (e : expr) : list term_var :=
  match e with
  | e_val _ => nil
  | e_app _ _ _ => nil
  | e_datacon _ _ _ _ => nil
  | e_let x _ e1 e2 =>
      expr_bound_term_vars e1 ++ x :: expr_bound_term_vars e2
  | e_letloc _ _ _ body => expr_bound_term_vars body
  | e_letregion _ body => expr_bound_term_vars body
  | e_case _ pats =>
      let fix go (ps : list pat) : list term_var :=
        match ps with
        | nil => nil
        | p :: ps' => pat_bound_term_vars p ++ go ps'
        end
      in go pats
  end.

Definition ty_loc_vars (t : ty) : list loc_var :=
  match t with
  | loc_ty _ l _ => [l]
  end.

Definition ty_region_vars (t : ty) : list region_var :=
  match t with
  | loc_ty _ _ r => [r]
  end.

Definition locexp_loc_vars (le : loc_exp) : list loc_var :=
  match le with
  | LE_Start _ => nil
  | LE_Next l _ => [l]
  | LE_After _ l _ => [l]
  end.

Definition locexp_region_vars (le : loc_exp) : list region_var :=
  match le with
  | LE_Start r => [r]
  | LE_Next _ r => [r]
  | LE_After _ _ r => [r]
  end.

Definition binds_loc_vars (binds : list (term_var * ty)) : list loc_var :=
  List.map bind_loc_var binds.

Definition binds_region_vars (binds : list (term_var * ty)) : list region_var :=
  List.map bind_region_var binds.

Fixpoint pat_occurs_term_vars (p : pat) : list term_var :=
  match p with
  | pat_clause _ binds body => pat_term_vars binds ++ expr_occurs_term_vars body
  end

with expr_occurs_term_vars (e : expr) : list term_var :=
  match e with
  | e_val v0 => val_term_vars v0
  | e_app _ _ vs => vals_term_vars vs
  | e_datacon _ _ _ vs => vals_term_vars vs
  | e_let x _ e1 e2 =>
      x :: expr_occurs_term_vars e1 ++ expr_occurs_term_vars e2
  | e_letloc _ _ _ body => expr_occurs_term_vars body
  | e_letregion _ body => expr_occurs_term_vars body
  | e_case v0 pats =>
      let fix go (ps : list pat) : list term_var :=
        match ps with
        | nil => nil
        | p :: ps' => pat_occurs_term_vars p ++ go ps'
        end
      in val_term_vars v0 ++ go pats
  end.

Fixpoint pat_occurs_loc_vars (p : pat) : list loc_var :=
  match p with
  | pat_clause _ binds body =>
      binds_loc_vars binds ++ expr_occurs_loc_vars body
  end

with expr_occurs_loc_vars (e : expr) : list loc_var :=
  match e with
  | e_val v0 => val_loc_vars v0
  | e_app _ locs vs =>
      loc_arg_loc_vars locs ++ vals_loc_vars vs
  | e_datacon _ l _ vs =>
      l :: vals_loc_vars vs
  | e_let _ T e1 e2 =>
      ty_loc_vars T ++ expr_occurs_loc_vars e1 ++ expr_occurs_loc_vars e2
  | e_letloc l _ le body =>
      l :: locexp_loc_vars le ++ expr_occurs_loc_vars body
  | e_letregion _ body => expr_occurs_loc_vars body
  | e_case v0 pats =>
      let fix go (ps : list pat) : list loc_var :=
        match ps with
        | nil => nil
        | p :: ps' => pat_occurs_loc_vars p ++ go ps'
        end
      in val_loc_vars v0 ++ go pats
  end.

Fixpoint pat_occurs_region_vars (p : pat) : list region_var :=
  match p with
  | pat_clause _ binds body =>
      binds_region_vars binds ++ expr_occurs_region_vars body
  end

with expr_occurs_region_vars (e : expr) : list region_var :=
  match e with
  | e_val v0 => val_region_vars v0
  | e_app _ locs vs =>
      loc_arg_regions locs ++ vals_region_vars vs
  | e_datacon _ _ r vs =>
      r :: vals_region_vars vs
  | e_let _ T e1 e2 =>
      ty_region_vars T ++ expr_occurs_region_vars e1 ++ expr_occurs_region_vars e2
  | e_letloc _ r le body =>
      r :: locexp_region_vars le ++ expr_occurs_region_vars body
  | e_letregion r body =>
      r :: expr_occurs_region_vars body
  | e_case v0 pats =>
      let fix go (ps : list pat) : list region_var :=
        match ps with
        | nil => nil
        | p :: ps' => pat_occurs_region_vars p ++ go ps'
        end
      in val_region_vars v0 ++ go pats
  end.

Fixpoint expr_occurs_laddrs (e : expr) : list laddr :=
  match e with
  | e_val v0 => val_symbolic_laddrs v0
  | e_app _ locs vs =>
      locs ++ vals_symbolic_laddrs vs
  | e_datacon _ l r vs =>
      (l, r) :: vals_symbolic_laddrs vs
  | e_let _ (loc_ty _ l r) e1 e2 =>
      (l, r) :: expr_occurs_laddrs e1 ++ expr_occurs_laddrs e2
  | e_letloc l r le body =>
      let le_laddrs :=
        match le with
        | LE_Start _ => nil
        | LE_Next l0 r0 => [(l0, r0)]
        | LE_After _ l0 r0 => [(l0, r0)]
        end in
      (l, r) :: le_laddrs ++ expr_occurs_laddrs body
  | e_letregion _ body => expr_occurs_laddrs body
  | e_case v0 pats =>
      let fix go (ps : list pat) : list laddr :=
        match ps with
        | nil => nil
        | pat_clause _ binds body :: ps' =>
            pat_laddrs binds ++ expr_occurs_laddrs body ++ go ps'
        end
      in val_symbolic_laddrs v0 ++ go pats
  end.

Fixpoint tick_marks (n : nat) : string :=
  match n with
  | O => ""
  | S n' => "'" ++ tick_marks n'
  end.

Definition term_var_with_ticks (x : term_var) (n : nat) : term_var :=
  match x with
  | mk_term_var s => mk_term_var (s ++ "$" ++ tick_marks n)
  end.

Definition loc_var_with_ticks (l : loc_var) (n : nat) : loc_var :=
  match l with
  | mk_loc_var s => mk_loc_var (s ++ "$" ++ tick_marks n)
  end.

Definition region_var_with_ticks (r : region_var) (n : nat) : region_var :=
  match r with
  | mk_region_var s => mk_region_var (s ++ "$" ++ tick_marks n)
  end.

Fixpoint fresh_term_var_from
    (base : term_var) (avoid : list term_var) (fuel : nat) : term_var :=
  match fuel with
  | O => term_var_with_ticks base O
  | S fuel' =>
      let cand := term_var_with_ticks base fuel in
      if in_dec term_var_eq_dec cand avoid
      then fresh_term_var_from base avoid fuel'
      else cand
  end.

Fixpoint fresh_loc_var_from
    (base : loc_var) (avoid : list loc_var) (fuel : nat) : loc_var :=
  match fuel with
  | O => loc_var_with_ticks base O
  | S fuel' =>
      let cand := loc_var_with_ticks base fuel in
      if in_dec loc_var_eq_dec cand avoid
      then fresh_loc_var_from base avoid fuel'
      else cand
  end.

Fixpoint fresh_region_var_from
    (base : region_var) (avoid : list region_var) (fuel : nat) : region_var :=
  match fuel with
  | O => region_var_with_ticks base O
  | S fuel' =>
      let cand := region_var_with_ticks base fuel in
      if in_dec region_var_eq_dec cand avoid
      then fresh_region_var_from base avoid fuel'
      else cand
  end.

Definition fresh_term_var (avoid : list term_var) (base : term_var) : term_var :=
  fresh_term_var_from base avoid (S (List.length avoid)).

Definition fresh_loc_var (avoid : list loc_var) (base : loc_var) : loc_var :=
  fresh_loc_var_from base avoid (S (List.length avoid)).

Definition fresh_region_var (avoid : list region_var) (base : region_var)
    : region_var :=
  fresh_region_var_from base avoid (S (List.length avoid)).

Definition rename_term_in_val
    (old_x new_x : term_var) (v0 : val) : val :=
  match v0 with
  | v_var x => if term_var_eq_dec old_x x then v_var new_x else v0
  | v_cloc _ _ _ _ => v0
  end.

Definition rename_term_in_bind
    (old_x new_x : term_var) (b : term_var * ty) : term_var * ty :=
  let '(x, T) := b in
  (if term_var_eq_dec old_x x then new_x else x, T).

Fixpoint rename_term_in_pat
    (old_x new_x : term_var) (p : pat) : pat :=
  match p with
  | pat_clause K binds body =>
      pat_clause K
        (List.map (rename_term_in_bind old_x new_x) binds)
        (rename_term_in_expr old_x new_x body)
  end

with rename_term_in_expr
    (old_x new_x : term_var) (e : expr) : expr :=
  match e with
  | e_val v0 => e_val (rename_term_in_val old_x new_x v0)
  | e_app f locs vs =>
      e_app f locs (List.map (rename_term_in_val old_x new_x) vs)
  | e_datacon K l r vs =>
      e_datacon K l r (List.map (rename_term_in_val old_x new_x) vs)
  | e_let x T e1 e2 =>
      e_let
        (if term_var_eq_dec old_x x then new_x else x)
        T
        (rename_term_in_expr old_x new_x e1)
        (rename_term_in_expr old_x new_x e2)
  | e_letloc l r le body =>
      e_letloc l r le (rename_term_in_expr old_x new_x body)
  | e_letregion r body =>
      e_letregion r (rename_term_in_expr old_x new_x body)
  | e_case v0 pats =>
      e_case (rename_term_in_val old_x new_x v0)
             (List.map (rename_term_in_pat old_x new_x) pats)
  end.

Definition rename_loc_in_laddr
    (old_lr : laddr) (new_l : loc_var) (a : laddr) : laddr :=
  let '(l, r) := a in
  (if laddr_eq_dec (l, r) old_lr then new_l else l, r).

Definition rename_loc_in_locexp
    (old_lr : laddr) (new_l : loc_var) (le : loc_exp) : loc_exp :=
  match le with
  | LE_Start r => LE_Start r
  | LE_Next l r => LE_Next (if laddr_eq_dec (l, r) old_lr then new_l else l) r
  | LE_After T l r =>
      LE_After T (if laddr_eq_dec (l, r) old_lr then new_l else l) r
  end.

Definition rename_loc_in_ty
    (old_lr : laddr) (new_l : loc_var) (t : ty) : ty :=
  match t with
  | loc_ty T l r => loc_ty T (if laddr_eq_dec (l, r) old_lr then new_l else l) r
  end.

Definition rename_loc_in_val
    (old_lr : laddr) (new_l : loc_var) (v0 : val) : val :=
  match v0 with
  | v_var _ => v0
  | v_cloc rc i l rg =>
      v_cloc rc i (if laddr_eq_dec (l, rg) old_lr then new_l else l) rg
  end.

Definition rename_loc_in_bind
    (old_lr : laddr) (new_l : loc_var) (b : term_var * ty) : term_var * ty :=
  (fst b, rename_loc_in_ty old_lr new_l (snd b)).

Fixpoint rename_loc_in_pat
    (old_lr : laddr) (new_l : loc_var) (p : pat) : pat :=
  match p with
  | pat_clause K binds body =>
      pat_clause K
        (List.map (rename_loc_in_bind old_lr new_l) binds)
        (rename_loc_in_expr old_lr new_l body)
  end

with rename_loc_in_expr
    (old_lr : laddr) (new_l : loc_var) (e : expr) : expr :=
  match e with
  | e_val v0 => e_val (rename_loc_in_val old_lr new_l v0)
  | e_app f locs vs =>
      e_app f
            (List.map (rename_loc_in_laddr old_lr new_l) locs)
            (List.map (rename_loc_in_val old_lr new_l) vs)
  | e_datacon K l r vs =>
      e_datacon K
                (if laddr_eq_dec (l, r) old_lr then new_l else l)
                r
                (List.map (rename_loc_in_val old_lr new_l) vs)
  | e_let x T e1 e2 =>
      e_let x
            (rename_loc_in_ty old_lr new_l T)
            (rename_loc_in_expr old_lr new_l e1)
            (rename_loc_in_expr old_lr new_l e2)
  | e_letloc l r le body =>
      e_letloc
        (if laddr_eq_dec (l, r) old_lr then new_l else l)
        r
        (rename_loc_in_locexp old_lr new_l le)
        (rename_loc_in_expr old_lr new_l body)
  | e_letregion r body =>
      e_letregion r (rename_loc_in_expr old_lr new_l body)
  | e_case v0 pats =>
      e_case (rename_loc_in_val old_lr new_l v0)
             (List.map (rename_loc_in_pat old_lr new_l) pats)
  end.

Definition rename_region_in_laddr
    (old_r new_r : region_var) (a : laddr) : laddr :=
  let '(l, r) := a in
  (l, if region_var_eq_dec old_r r then new_r else r).

Definition rename_region_in_locexp
    (old_r new_r : region_var) (le : loc_exp) : loc_exp :=
  match le with
  | LE_Start r => LE_Start (if region_var_eq_dec old_r r then new_r else r)
  | LE_Next l r => LE_Next l (if region_var_eq_dec old_r r then new_r else r)
  | LE_After T l r =>
      LE_After T l (if region_var_eq_dec old_r r then new_r else r)
  end.

Definition rename_region_in_ty
    (old_r new_r : region_var) (t : ty) : ty :=
  match t with
  | loc_ty T l r => loc_ty T l (if region_var_eq_dec old_r r then new_r else r)
  end.

Definition rename_region_in_val
    (old_r new_r : region_var) (v0 : val) : val :=
  match v0 with
  | v_var _ => v0
  | v_cloc rc i l rg =>
      v_cloc
        (if region_var_eq_dec old_r rc then new_r else rc)
        i
        l
        (if region_var_eq_dec old_r rg then new_r else rg)
  end.

Definition rename_region_in_bind
    (old_r new_r : region_var) (b : term_var * ty) : term_var * ty :=
  (fst b, rename_region_in_ty old_r new_r (snd b)).

Fixpoint rename_region_in_pat
    (old_r new_r : region_var) (p : pat) : pat :=
  match p with
  | pat_clause K binds body =>
      pat_clause K
        (List.map (rename_region_in_bind old_r new_r) binds)
        (rename_region_in_expr old_r new_r body)
  end

with rename_region_in_expr
    (old_r new_r : region_var) (e : expr) : expr :=
  match e with
  | e_val v0 => e_val (rename_region_in_val old_r new_r v0)
  | e_app f locs vs =>
      e_app f
            (List.map (rename_region_in_laddr old_r new_r) locs)
            (List.map (rename_region_in_val old_r new_r) vs)
  | e_datacon K l r vs =>
      e_datacon K
                l
                (if region_var_eq_dec old_r r then new_r else r)
                (List.map (rename_region_in_val old_r new_r) vs)
  | e_let x T e1 e2 =>
      e_let x
            (rename_region_in_ty old_r new_r T)
            (rename_region_in_expr old_r new_r e1)
            (rename_region_in_expr old_r new_r e2)
  | e_letloc l r le body =>
      e_letloc
        l
        (if region_var_eq_dec old_r r then new_r else r)
        (rename_region_in_locexp old_r new_r le)
        (rename_region_in_expr old_r new_r body)
  | e_letregion r body =>
      e_letregion
        (if region_var_eq_dec old_r r then new_r else r)
        (rename_region_in_expr old_r new_r body)
  | e_case v0 pats =>
      e_case (rename_region_in_val old_r new_r v0)
             (List.map (rename_region_in_pat old_r new_r) pats)
  end.

Fixpoint rename_terms_in_expr
    (rens : list (term_var * term_var)) (e : expr) : expr :=
  match rens with
  | nil => e
  | (old_x, new_x) :: rens' =>
      rename_terms_in_expr rens' (rename_term_in_expr old_x new_x e)
  end.

Fixpoint rename_locs_in_expr
    (rens : list (laddr * loc_var)) (e : expr) : expr :=
  match rens with
  | nil => e
  | (old_lr, new_l) :: rens' =>
      rename_locs_in_expr rens' (rename_loc_in_expr old_lr new_l e)
  end.

Fixpoint rename_regions_in_expr
    (rens : list (region_var * region_var)) (e : expr) : expr :=
  match rens with
  | nil => e
  | (old_r, new_r) :: rens' =>
      rename_regions_in_expr rens' (rename_region_in_expr old_r new_r e)
  end.

Fixpoint freshen_expr_with
    (avoid_t : list term_var)
    (avoid_l : list laddr)
    (avoid_r : list region_var)
    (e : expr)
    {struct e}
    : expr :=
  match e with
  | e_val v0 => e_val v0
  | e_app f locs vs => e_app f locs vs
  | e_datacon K l r vs => e_datacon K l r vs
  | e_let x T e1 e2 =>
      let e1' := freshen_expr_with avoid_t avoid_l avoid_r e1 in
      let avoid_t0 :=
        avoid_t ++ remove term_var_eq_dec x (expr_occurs_term_vars e2) in
      let x' :=
        if in_dec term_var_eq_dec x avoid_t0
        then fresh_term_var avoid_t0 x
        else x in
      let e2' := freshen_expr_with (x' :: avoid_t) avoid_l avoid_r e2 in
      e_let x' T e1'
            (if term_var_eq_dec x x'
             then e2'
             else rename_term_in_expr x x' e2')
  | e_letloc l r le body =>
      let lr := (l, r) in
      let avoid_l0 :=
        avoid_l ++ remove laddr_eq_dec lr (expr_occurs_laddrs body) in
      let l' :=
        if in_dec laddr_eq_dec lr avoid_l0
        then fresh_loc_var (List.map fst avoid_l0) l
        else l in
      let body' :=
        freshen_expr_with avoid_t ((l', r) :: avoid_l) avoid_r body in
      e_letloc l' r le
               (if loc_var_eq_dec l l'
                then body'
                else rename_loc_in_expr (l, r) l' body')
  | e_letregion r body =>
      let avoid_r0 :=
        avoid_r ++ remove region_var_eq_dec r (expr_occurs_region_vars body) in
      let r' :=
        if in_dec region_var_eq_dec r avoid_r0
        then fresh_region_var avoid_r0 r
        else r in
      let body' := freshen_expr_with avoid_t avoid_l (r' :: avoid_r) body in
      e_letregion r'
                  (if region_var_eq_dec r r'
                   then body'
                   else rename_region_in_expr r r' body')
  | e_case v0 pats =>
      let fix go_pats (ps : list pat) : list pat :=
        match ps with
        | nil => nil
        | pat_clause K binds body :: ps' =>
            let fix go_binds
                (avoid_t : list term_var)
                (avoid_l : list laddr)
                (avoid_r : list region_var)
                (binds : list (term_var * ty))
                {struct binds}
                : list (term_var * ty)
                  * list (term_var * term_var)
                  * list (laddr * loc_var)
                  * list (region_var * region_var) :=
              match binds with
              | nil => (nil, nil, nil, nil)
              | (x, loc_ty T l r) :: binds' =>
                  let lr := (l, r) in
                  let avoid_t0 :=
                    avoid_t ++ pat_term_vars binds'
                    ++ remove term_var_eq_dec x (expr_occurs_term_vars body) in
                  let x' :=
                    if in_dec term_var_eq_dec x avoid_t0
                    then fresh_term_var avoid_t0 x
                    else x in
                  let avoid_l0 :=
                    avoid_l ++ pat_laddrs binds'
                    ++ remove laddr_eq_dec lr (expr_occurs_laddrs body) in
                  let l' :=
                    if in_dec laddr_eq_dec lr avoid_l0
                    then fresh_loc_var (List.map fst avoid_l0) l
                    else l in
                  let avoid_r0 :=
                    avoid_r ++ binds_region_vars binds'
                    ++ remove region_var_eq_dec r (expr_occurs_region_vars body) in
                  let r' :=
                    if in_dec region_var_eq_dec r avoid_r0
                    then fresh_region_var avoid_r0 r
                    else r in
                  let '(binds'', trens, lrens, rrens) :=
                    go_binds
                      (x' :: avoid_t)
                      ((l', r) :: avoid_l)
                      (r' :: avoid_r)
                      binds' in
                  ((x', loc_ty T l' r') :: binds'',
                   (x, x') :: trens,
                   ((l, r), l') :: lrens,
                   (r, r') :: rrens)
              end in
            let '(binds', trens, lrens, rrens) :=
              go_binds avoid_t avoid_l avoid_r binds in
            let body' :=
              freshen_expr_with
                (pat_term_vars binds' ++ avoid_t)
                (pat_laddrs binds' ++ avoid_l)
                (binds_region_vars binds' ++ avoid_r)
                body in
            let body'' :=
              rename_regions_in_expr rrens
                (rename_locs_in_expr lrens
                  (rename_terms_in_expr trens body')) in
            pat_clause K binds' body'' :: go_pats ps'
        end in
      e_case v0 (go_pats pats)
  end.

End LoCalSyntax.
