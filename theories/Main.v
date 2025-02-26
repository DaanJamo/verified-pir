From Coq.Strings Require Import String.
#[local] Open Scope string_scope.

From SimpleIO Require Import SimpleIO.
Import IO.Notations.

From VTL Require Import Translation Printer.

Definition test_file := ((translate_term remap_env identity_EAst) ann_id).
Eval cbv in (print_as_program test_file).
Definition main : IO unit :=
  chan <- open_out "test.pir" ;;
  output_string chan (print_as_program test_file) ;;
  close_out chan
.

RunIO main.
