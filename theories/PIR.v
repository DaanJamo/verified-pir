Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.
Require Import FunInd.

Set Implicit Arguments.

Require Import Coq.Program.Basics.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Restricted version of the AST from plutus-cert *)

Inductive DefaultUni :=
  | DefaultUniInteger
  | DefaultUniBool
  | DefaultUniUnit
.

(** Coq interpretation of plutus built-in types of base kind. If not of
* base-kind (or not well-kinded), returns None.
*)
Definition uniType_option (x : DefaultUni) : option Set :=
  match x with
    | DefaultUniInteger    => Some Z
    (* | DefaultUniByteString => Some (list byte) *)
    (* | DefaultUniString => Some (list byte) UTF-8 encoded strings *)
    | DefaultUniUnit => Some unit
    (* | DefaultUniData => Some Data *)
    (* | DefaultUniBLS12_381_G1_Element => Some Z *)
    (* | DefaultUniBLS12_381_G2_Element => Some Z *)
    (* | DefaultUniBLS12_381_MlResult => Some Z *)
    | DefaultUniBool => Some bool

    (* | DefaultUniApply DefaultUniProtoList t =>
      match uniType_option t with
        | None => None
        | Some A => Some (list A)
      end *)

    (* | DefaultUniApply (DefaultUniApply DefaultUniProtoPair s) t =>
      match uniType_option s, uniType_option t with
      | Some A, Some B => Some (prod A B)
      | _, _ => None
      end

    | DefaultUniApply _ _ => None
    | DefaultUniProtoList => None
    | DefaultUniProtoPair => None *)
  end
.
Functional Scheme uniType_option_rect := Induction for uniType_option Sort Type.

(** Coq interpretation of plutus built-in types of base kind. Used for constructing
constants (See term.Constant). Types that are ill-kinded or do not have base kind are
mapped to the empty type, ensuring that Constants of such type can be constructed.
*)
Definition uniType (x : DefaultUni) : Type :=
  match uniType_option x with
    | None => Empty_set
    | Some ty => ty
  end.

(* Constants are coq values of the interpretation of some type in
   DefaultUni *)
Inductive constant :=
  ValueOf : forall (T : DefaultUni), uniType T -> constant.

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
  | IfThenElse
.

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  (* | Ty_Var : tyname -> ty *)
  | Ty_Fun : ty -> ty -> ty
  (* | Ty_IFix : ty -> ty -> ty *)
  (* | Ty_Forall : binderTyname -> kind -> ty -> ty *)
  | Ty_Builtin : DefaultUni -> ty
  (* | Ty_Lam : binderTyname -> kind -> ty -> ty *)
  (* | Ty_App : ty -> ty -> ty *)
  (* | Ty_SOP : list (list ty) -> ty *)
  | UNDEFINED : string -> ty
.

Inductive term :=
  | Var      : name -> term
  | LamAbs   : binderName -> ty -> term -> term
  | Apply    : term -> term -> term
  | Builtin  : DefaultFun -> term
  | Constant : constant -> term
  | Error    : ty -> term
.

Declare Scope plutus_scope.

Declare Custom Entry plutus_term.
Declare Custom Entry plutus_ty.
Declare Custom Entry plutus_kind.

Module PlutusNotations.

  Notation "<{ e }>" := e (e custom plutus_term at level 99) : plutus_scope.
  Notation "<{{ e }}>" := e (e custom plutus_ty at level 99) : plutus_scope.
  Notation "<{{{ e }}}>" := e (e custom plutus_kind at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_term, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_ty, x at level 99) : plutus_scope.
  Notation "( x )" := x (in custom plutus_kind, x at level 99) : plutus_scope.
  Notation "x" := x (in custom plutus_term at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_ty at level 0, x constr at level 0) : plutus_scope.
  Notation "x" := x (in custom plutus_kind at level 0, x constr at level 0) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_term at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_ty at level 1, x constr) : plutus_scope.
  Notation "{ x }" := x (in custom plutus_kind at level 1, x constr) : plutus_scope.


  #[global]
  Open Scope plutus_scope.

  (* Term notations *)
  Notation "'λ' x :: ty , body" := (LamAbs x ty body) (in custom plutus_term at level 51, right associativity).
  (* Notation "'Λ' X :: K , body" := (TyAbs X K body) (in custom plutus_term at level 51, right associativity). *)
  Notation "t1 ⋅ t2" := (Apply t1 t2) (in custom plutus_term at level 50, left associativity).
  (* Notation "t @ T" := (TyInst t T) (in custom plutus_term at level 50, left associativity). *)


  (* Builtin notations *)
  Notation "(+)" := (Builtin AddInteger) (in custom plutus_term).
  Notation "'ifthenelse'" := (Builtin IfThenElse).
  Notation "t1 '==' t2" := (<{ {Builtin EqualsInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, no associativity).
  Notation "t1 '+' t2" := (<{ {Builtin AddInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
  Notation "t1 '-' t2" := (<{ {Builtin SubtractInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
  Notation "t1 '*' t2" := (<{ {Builtin MultiplyInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).

  (* / collides with substitution notation *)
  (*
  Notation "t1 '/' t2" := (<{ {Builtin DivideInteger} ⋅ t1 ⋅ t2 }>)
    (in custom plutus_term at level 50, left associativity).
      *)

  (* Constants *)
  Notation "'CInt' x" := (Constant (ValueOf DefaultUniInteger x)) (in custom plutus_term at level 49).
  Notation "'CBool' x" := (Constant (ValueOf DefaultUniBool x)) (in custom plutus_term at level 49).
  (* Notation "'CBS' xs" := (Constant (ValueOf DefaultUniByteString xs)) (in custom plutus_term at level 49). *)
  Notation "'()'" := (Constant (ValueOf DefaultUniUnit tt)) (in custom plutus_term).
  Notation "'true'" := (Constant (ValueOf DefaultUniBool true)) (in custom plutus_term).
  Notation "'false'" := (Constant (ValueOf DefaultUniBool false)) (in custom plutus_term).

  (* Built-in types *)
  Notation "'ℤ'" := (Ty_Builtin DefaultUniInteger) (in custom plutus_term).
  Notation "'bool'" := (Ty_Builtin DefaultUniBool) (in custom plutus_term).
  Notation "'unit'" := (Ty_Builtin DefaultUniUnit) (in custom plutus_term).
  Notation "X '→' Y" := (Ty_Fun X Y) (in custom plutus_term at level 49, right associativity).
  (* Notation "'bytestring'" := (Ty_Builtin DefaultUniByteString) (in custom plutus_term at level 51, right associativity). *)

  (* String notation for list byte (bytestring and string)

  Pretty-print values of type list byte (used for pir's bytestring and string
  representation) as string literals, for readability.

  The parsing function will always fail, as we won't accept string literal
  notation in the parser, which has different mechanisms in Haskell and Coq
  *)

  (* String Notation requires a monomorphised type *)
  Notation bytes := (list byte) (only parsing).

  Definition parse_bytes (x : bytes) := x.
  Definition print_bytes (x : bytes) := x.

  String Notation bytes parse_bytes print_bytes : plutus_scope.

End PlutusNotations.
