From Coq Require Import Program.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Transform config.

From VTL.Simple Require Import DBToPIR.
From VTL.Semantics Require Import BigStepPIR.

(* A end-to-end pipeline from Coq/Gallina terms to PIR terms (with bogus types):
   Gallina ▷ TemplateRocq ▷ PCUIC ▷ λ□/EAst (without box type annotations) ▷ DB ▷ PIR *)

Import Common.Transform.Transform.
#[local] Obligation Tactic := program_simpl.

Definition default_pir_fuel := 5000.

Definition tm_program  := unit × tm.
Definition pir_program := unit × term.

Definition eval_tm_program  (p : tm_program)  (v  : tm)   := ∥ DBToPIR.eval p.2 v ∥.
Definition eval_pir_program (p : pir_program) (v' : term) := ∥ BigStepPIR.eval p.2 v' default_pir_fuel ∥.

Axiom translate_named : tm -> term.
Definition translate_named_program (p : tm_program) := (tt, translate_named p.2).

Program Definition stlc_to_pir_transform :
  Transform.t unit unit tm term tm term
  eval_tm_program
  eval_pir_program :=
  {| name := "translate stlc to pir terms";
     transform input _ := _;
     obseq p _ p' v v' := translatesTo [] v v' ;
  |}.
Next Obligation.
(* pre? *) exact True.
Qed.
Next Obligation.
(* pre is true of input *) Admitted.
Next Obligation.
(* post *) exact True.
Qed.
Next Obligation.
(* pre establishes post *)
Admitted.
Next Obligation.
  (* exact (translate_correct p.2 v p'.2 (∥ evalNamed p.2 v ∥) (∥ eval p'.2 v'∥)). *)
Admitted.

Check run stlc_to_pir_transform.
