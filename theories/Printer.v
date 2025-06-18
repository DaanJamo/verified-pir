From Coq Require Import String BinInt List.

(* printer for dumping pretty-printed PIR terms to check with the Plutus CLI tool *)
(* From SimpleIO Require Import SimpleIO. *)
From QuickChick Require Import Show.

From VTL Require Import PIR Pretty Translation.

Import PlutusNotations ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition identity_ast : term :=

  <{ λ "x" :: ℤ, {Var "x"} }>.

Definition plus_ast : term :=
  <{ (λ "x" :: ℤ, λ "y" :: ℤ, {Var "x"} + {Var "y"}) ⋅ CInt 1 }>.

(* Import IO.Notations. *)

(* Set stdin/stdout so we can run main from the command line *)
(* RunIO IOMode Forward. *)
(* Automatically assign the right integer types (hopefully) *)
(* RunIO Smart On. *)

(* We test the pipeline starting from the λ□ identity function *)
Definition test_pir_ast := (translate_unsafe nil identity_EAst ann_id).
Eval cbv in (print_as_program test_pir_ast).
(* Definition main : IO unit :=
  chan <- open_out "./output/test.pir" ;;
  output_string chan (print_as_program test_pir_ast) ;;
  close_out chan. *)

(* Getting errors: PrimFloat.float PrimInt63.int have to be realized *)
(* RunIO main. *)
