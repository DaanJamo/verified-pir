From Coq Require Import String BinInt List.

(* printing functionality *)
From SimpleIO Require Import SimpleIO.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

From VTL Require Import PIR Pretty Translation.

(* λ(x : Int) . x *)
Definition identity_ast : term :=
  LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x")
.

Definition plus_ast : term :=
  (Apply
    (LamAbs "x" (Ty_Builtin DefaultUniInteger)
      (LamAbs "y" (Ty_Builtin DefaultUniInteger)
        (Apply (Apply (Builtin AddInteger) (Var "x")) (Var "y"))))
  (Constant (ValueOf DefaultUniInteger 1))).*)

(* Definition let_ast : term :=
  (Let NonRec 
    [(TermBind Strict 
        (VarDecl "x" (Ty_Builtin DefaultUniInteger)) 
        (Error (Ty_Builtin DefaultUniInteger)))]
    (Apply 
      (Apply (Builtin EqualsInteger) 
             (Apply 
                (Apply (Builtin AddInteger) (Constant (ValueOf DefaultUniInteger 10)))
                (Var "x")))
      (Constant (ValueOf DefaultUniInteger 5)))). *)


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
