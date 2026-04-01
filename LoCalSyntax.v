Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import List.
Import ListNotations.

Module LoCalSyntax.

(* A first syntax-only draft of the LoCal core language, following the
   grammar in thesis §2.2 (Formal Language and Grammar). *)

Inductive loc_exp : Type :=
  | LE_Start : string -> loc_exp
  | LE_Next : string -> string -> loc_exp
  | LE_After : string -> string -> string -> loc_exp.

Inductive hty : Type :=
  | HT_Located : string -> string -> string -> hty.

Inductive val : Type :=
  | v_var : string -> val
  | v_cloc : string -> nat -> string -> string -> val.

Inductive pat : Type :=
  | pat_clause : string -> list (string * hty) -> expr -> pat
with expr : Type :=
  | e_val : val -> expr
  | e_app : string -> list (string * string) -> list val -> expr
  | e_datacon : string -> string -> string -> list val -> expr
  | e_let : string -> hty -> expr -> expr -> expr
  | e_letloc : string -> string -> loc_exp -> expr -> expr
  | e_letregion : string -> expr -> expr
  | e_case : val -> list pat -> expr.

Inductive datatype_decl : Type :=
  | DataDecl : string -> list (string * list string) -> datatype_decl.

Inductive fdecl : Type :=
  | FunDecl : string -> list (string * string) -> list hty -> hty -> list string -> expr -> fdecl.

Record program : Type := Program
  { prog_ddecls : list datatype_decl;
    prog_fdecls : list fdecl;
    prog_main : expr }.

Declare Custom Entry local_hty.
Declare Custom Entry local_val.
Declare Custom Entry local_exp.
Declare Scope local_scope.

Notation "<{{ t }}>" := t (t custom local_hty at level 200).
Notation "<{ e }>" := e (e custom local_exp at level 200).

Notation "'at' T '@' l '^' r" :=
  (HT_Located T l r)
    (in custom local_hty at level 80, T constr, l constr, r constr)
    : local_scope.

Notation "'v' x" := (v_var x)
  (in custom local_val at level 10, x constr) : local_scope.

Notation "'cloc' '(' r ',' i ',' l '^' rg ')'" := (v_cloc r i l rg)
  (in custom local_val at level 10, r constr, i constr, l constr, rg constr)
  : local_scope.

Notation "'start' r" := (LE_Start r)
  (in custom local_exp at level 10, r constr) : local_scope.

Notation "l '^' r '+1'" := (LE_Next l r)
  (in custom local_exp at level 40, l constr, r constr) : local_scope.

Notation "'after' T '@' l '^' r" := (LE_After T l r)
  (in custom local_exp at level 40, T constr, l constr, r constr) : local_scope.

Notation "'letloc' l '^' r '=' le 'in' e" :=
  (e_letloc l r le e)
    (in custom local_exp at level 80,
      l constr, r constr, le custom local_exp, e custom local_exp)
    : local_scope.

Notation "'letregion' r 'in' e" :=
  (e_letregion r e)
    (in custom local_exp at level 80, r constr, e custom local_exp)
    : local_scope.

Notation "'let' x ':' T '=' e1 'in' e2" :=
  (e_let x T e1 e2)
    (in custom local_exp at level 80,
      x constr, T custom local_hty, e1 custom local_exp, e2 custom local_exp)
    : local_scope.

Notation "'case' scrut 'of' branches" :=
  (e_case scrut branches)
    (in custom local_exp at level 80, scrut constr, branches constr)
    : local_scope.

Open Scope local_scope.

End LoCalSyntax.
