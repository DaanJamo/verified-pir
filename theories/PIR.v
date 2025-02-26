From Coq Require Import String.
Local Open Scope string_scope.
(* Restricted version of the AST from plutus-cert *)

Inductive DefaultUni :=
  | DefaultUniInteger
  | DefaultUniBool
  | DefaultUniUnit
.

Inductive DefaultFun :=
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
.

Inductive ty :=
  | Ty_Builtin : DefaultUni -> ty
  | Ty_Fun : ty -> ty -> ty
  | UNDEFINED : string -> ty (* debug type *)
.

(* for now, we trust the string representing a value is correct *)
Inductive term :=
  | Var      : string -> term
  | LamAbs   : string -> ty -> term -> term
  | App      : term -> term -> term
  | Builtin  : DefaultFun -> term
  | Constant : ty -> string -> term
.
