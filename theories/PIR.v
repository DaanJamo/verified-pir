Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

Set Implicit Arguments.

Require Import Coq.Program.Basics.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Exports FunInd and used for tests later *)
From QuickChick Require Import QuickChick.
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

(* for now, we trust the string representing a value is correct *)
Inductive term :=
  | Var      : name -> term
  | LamAbs   : binderName -> ty -> term -> term
  | Apply    : term -> term -> term
  | Builtin  : DefaultFun -> term
  | Constant : constant -> term
.
