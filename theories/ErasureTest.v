From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.
Import MCMonadNotation.

Print erase_and_print_template_program.
Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

MetaCoq Test Quote (fun x => x).
MetaCoq Test Quote (fun (f : nat -> nat) (x : nat) => f x).
MetaCoq Quote Recursively Definition zero := 0.
MetaCoq Quote Recursively Definition idq := ((fun x => x + x) 3).

Locate typed_erasure_pipeline.
Eval cbv in erase_and_print_template_program default_erasure_config [] idq.
