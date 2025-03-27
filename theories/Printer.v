From Coq Require Import String BinInt List.

(* printing functionality *)
From SimpleIO Require Import SimpleIO.

Import ListNotations.

From VTL Require Import PIR Pretty Translation.
Import PlutusNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition identity_ast : term :=
  <{ λ "x" :: ℤ, {Var "x"} }>
.

Definition plus_ast : term :=
  <{ (λ "x" :: ℤ, λ "y" :: ℤ, {Var "x"} + {Var "y"}) ⋅ CInt 1 }>.

(* Definition let_ast : term :=
 (Let NonRec [(TermBind Strict (VarDecl "x" ℤ) (Error ℤ))] 
    <{ CInt 10 + {Var "x"} + CInt 5 }>). *)

Import IO.Notations.

(* Set stdin/stdout so we can run main from the command line *)
RunIO IOMode Forward.
(* Automatically assign the right integer types (hopefully) *)
RunIO Smart On.

Definition test_pir_ast := ((translate_term remap_env identity_EAst) ann_id).
Eval cbv in (print_as_program test_pir_ast).
Definition main : IO unit :=
  chan <- open_out "./output/test.pir" ;;
  output_string chan (print_as_program test_pir_ast) ;;
  close_out chan
.

(* RunIO main. *)
