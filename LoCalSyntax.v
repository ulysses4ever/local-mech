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

Lemma tycon_eq_dec : forall (a b : tycon), {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

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
  (subst_lvar lo ln (fst a), subst_rvar ro rn (snd a)).

Definition subst_loc_in_locexp
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (le : loc_exp) : loc_exp :=
  match le with
  | LE_Start r => LE_Start (subst_rvar ro rn r)
  | LE_Next l r => LE_Next (subst_lvar lo ln l) (subst_rvar ro rn r)
  | LE_After T l r => LE_After T (subst_lvar lo ln l) (subst_rvar ro rn r)
  end.

Definition subst_loc_in_ty
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (t : ty) : ty :=
  match t with
  | loc_ty T l r => loc_ty T (subst_lvar lo ln l) (subst_rvar ro rn r)
  end.

Definition subst_loc_in_val
    (lo : loc_var) (ro : region_var)
    (ln : loc_var) (rn : region_var)
    (v0 : val) : val :=
  match v0 with
  | v_var _ => v0
  | v_cloc r i l rg =>
      v_cloc (subst_rvar ro rn r) i (subst_lvar lo ln l) (subst_rvar ro rn rg)
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

Definition val_term_vars (v0 : val) : list term_var :=
  match v0 with
  | v_var x => [x]
  | v_cloc _ _ _ _ => nil
  end.

Definition val_symbolic_laddrs (v0 : val) : list laddr :=
  match v0 with
  | v_var _ => nil
  | v_cloc _ _ l r => [(l, r)]
  end.

Definition val_symbolic_regions (v0 : val) : list region_var :=
  match v0 with
  | v_var _ => nil
  | v_cloc _ _ _ r => [r]
  end.

Definition vals_term_vars (vs : list val) : list term_var :=
  flat_map val_term_vars vs.

Definition vals_symbolic_laddrs (vs : list val) : list laddr :=
  flat_map val_symbolic_laddrs vs.

Definition vals_symbolic_regions (vs : list val) : list region_var :=
  flat_map val_symbolic_regions vs.

Definition loc_arg_regions (loc_args : list laddr) : list region_var :=
  List.map snd loc_args.

(* The thesis assumes an implicit uniquify discipline:
   all binders for values, locations, and regions are distinct.
   We expose the corresponding binder collections here so the rest of the
   mechanization can state that invariant explicitly when needed. *)

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

Fixpoint pat_bound_laddrs (p : pat) : list laddr :=
  match p with
  | pat_clause _ binds body => pat_laddrs binds ++ expr_bound_laddrs body
  end

with expr_bound_laddrs (e : expr) : list laddr :=
  match e with
  | e_val _ => nil
  | e_app _ _ _ => nil
  | e_datacon _ _ _ _ => nil
  | e_let _ _ e1 e2 =>
      expr_bound_laddrs e1 ++ expr_bound_laddrs e2
  | e_letloc l r _ body => (l, r) :: expr_bound_laddrs body
  | e_letregion _ body => expr_bound_laddrs body
  | e_case _ pats =>
      let fix go (ps : list pat) : list laddr :=
        match ps with
        | nil => nil
        | p :: ps' => pat_bound_laddrs p ++ go ps'
        end
      in go pats
  end.

Fixpoint pat_bound_regions (p : pat) : list region_var :=
  match p with
  | pat_clause _ _ body => expr_bound_regions body
  end

with expr_bound_regions (e : expr) : list region_var :=
  match e with
  | e_val _ => nil
  | e_app _ _ _ => nil
  | e_datacon _ _ _ _ => nil
  | e_let _ _ e1 e2 =>
      expr_bound_regions e1 ++ expr_bound_regions e2
  | e_letloc _ _ _ body => expr_bound_regions body
  | e_letregion r body => r :: expr_bound_regions body
  | e_case _ pats =>
      let fix go (ps : list pat) : list region_var :=
        match ps with
        | nil => nil
        | p :: ps' => pat_bound_regions p ++ go ps'
        end
      in go pats
  end.

Definition expr_binders_unique (e : expr) : Prop :=
  NoDup (expr_bound_term_vars e)
  /\ NoDup (expr_bound_laddrs e)
  /\ NoDup (expr_bound_regions e).

Definition fdecl_bound_term_vars (fd : fdecl) : list term_var :=
  match fd with
  | FunDecl _ _ named_args _ _ body =>
      List.map fst named_args ++ expr_bound_term_vars body
  end.

Definition fdecl_bound_laddrs (fd : fdecl) : list laddr :=
  match fd with
  | FunDecl _ locs _ _ _ body =>
      locs ++ expr_bound_laddrs body
  end.

Definition fdecl_bound_regions (fd : fdecl) : list region_var :=
  match fd with
  | FunDecl _ _ _ _ regions body =>
      regions ++ expr_bound_regions body
  end.

Definition fdecl_binders_unique (fd : fdecl) : Prop :=
  NoDup (fdecl_bound_term_vars fd)
  /\ NoDup (fdecl_bound_laddrs fd)
  /\ NoDup (fdecl_bound_regions fd).

(* Freshen(FD) in the thesis discharges exactly this no-capture
   condition before function-body substitution.  We expose the
   side condition at the shared syntax layer so both the static and
   dynamic developments can state it explicitly. *)
Definition app_subst_fresh
    (body : expr) (loc_args : list laddr) (val_args : list val) : Prop :=
  (forall x,
      In x (vals_term_vars val_args) ->
      ~ In x (expr_bound_term_vars body))
  /\
  (forall lr,
      In lr (loc_args ++ vals_symbolic_laddrs val_args) ->
      ~ In lr (expr_bound_laddrs body))
  /\
  (forall r,
      In r (loc_arg_regions loc_args ++ vals_symbolic_regions val_args) ->
      ~ In r (expr_bound_regions body)).

Definition program_binders_unique (p : program) : Prop :=
  Forall fdecl_binders_unique (prog_fdecls p)
  /\ expr_binders_unique (prog_main p).

End LoCalSyntax.
