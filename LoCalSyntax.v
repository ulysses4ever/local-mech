Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.

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

Definition pat_field_tycons (binds : list (term_var * ty)) : list tycon :=
  List.map (fun '(_, loc_ty T _ _) => T) binds.

Definition pat_term_vars (binds : list (term_var * ty)) : list term_var :=
  List.map fst binds.

End LoCalSyntax.
