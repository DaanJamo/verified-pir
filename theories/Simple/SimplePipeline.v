From Coq Require Import Program.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst Transform config.
From MetaCoq.Template Require Import TemplateMonad Loader.
From MetaCoq.Erasure Require Import EAst EProgram EWcbvEval.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.

From VTL.Simple Require Import EAstToDB DBToPIR.
From VTL.Semantics Require Import BigStepPIR.

(* A end-to-end pipeline from Coq/Gallina terms to PIR terms (with bogus types):
   Gallina ▷ TemplateRocq ▷ PCUIC ▷ λ□/EAst (without box type annotations) ▷ DB ▷ PIR *)

Import MCMonadNotation.
Import Common.Transform.Transform.
#[local] Obligation Tactic := program_simpl.

Definition default_pir_fuel := 5000.

Definition tm_program  := unit × tm.
Definition pir_program := unit × term.

Definition eval_tm_program  (p : tm_program)  (v  : tm)   := ∥ DBToPIR.eval p.2 v ∥.
Definition eval_pir_program (p : pir_program) (v' : term) := ∥ exists k, BigStepPIR.eval p.2 v' k ∥.

Definition translatable_et (p : eprogram) : Prop :=
  let '(_, et) := p in
  exists t, translate_et [] et = Some t.
Definition translate_erased_program p (pre : translatable_et p) := 
  match translate_et [] p.2 with
  | Some t => (tt, t)
  | None => (tt, tm_oops) end.

Definition translatable_tm (p : tm_program) : Prop := 
  let '(_, t) := p in
  exists t', translate_term [] t = Some t'. 
Definition translate_stlc_program p (pre : translatable_tm p) := (tt, translate_unsafe p.2).

Program Definition east_to_stlc_transform :
  Transform.t global_context unit EAst.term tm EAst.term tm
  (eval_eprogram final_wcbv_flags) 
  eval_tm_program :=
  {| name := "translate lambda box to stlc" ;
     pre := translatable_et ;
     transform := translate_erased_program ;
     post _ := True ;
     obseq ep _ p ev v := True ;
     preservation _ _ _ _ := _
  |}.
Next Obligation.
  unfold translatable_et in t1.
  destruct p as [env et] eqn:H.
  destruct t1 as [t2 tl].
  destruct e. exists t2.
  split. unfold eval_tm_program. sq.
  unfold translate_erased_program. simpl. 
  rewrite tl. simpl in *.
Admitted.

(* Lemma translate_program_correct *)

Lemma compose_translate_term : forall Γ t t',
  translate_et Γ t = Some t' ->
  exists t'', translate_term (map bytestring.String.to_string Γ) t' = Some t''.
Proof.
Admitted.

Lemma compose_translatable : forall p,
  translatable_et p ->
  exists p', translatable_tm p'.
Proof.
  intros p tl.
  destruct p.
  unfold translatable_et in tl.
  destruct tl. apply compose_translate_term in H as [t'' H'].
  exists (tt, x). unfold translatable_tm. exists t''. simpl in H'.
  assumption.
Admitted.

Program Definition stlc_to_pir_transform :
  Transform.t unit unit tm term tm term
  eval_tm_program
  eval_pir_program :=
  {| name := "translate stlc to pir terms";
     pre := translatable_tm;
     transform := translate_stlc_program;
     post _ := True;
     obseq p _ p' v v' := translatesTo [] v v';
     preservation _ _ _ _ := _
  |}.
Next Obligation.
  unfold translatable_tm in t1.
  destruct p as [env t] eqn:H.
  destruct t1 as [t' tl].
  destruct e.
  specialize (translate_correct t t0 t' H0 tl).
  unfold translate_stlc_program. unfold eval_pir_program.
  intros tlt.
  destruct tlt as [v' [fuel [tlt ev]]].
  exists v'. split.
  - sq. exists fuel. simpl. 
    unfold translate_unsafe. 
    now rewrite tl.
  - assumption.
Qed.

Program Definition partial_pipeline :
  Transform.t _ _ _ term _ term
  (eval_eprogram final_wcbv_flags) 
  eval_pir_program :=
  east_to_stlc_transform ▷
  stlc_to_pir_transform.
Next Obligation.
Admitted.

Program Definition simple_pipeline :
  Transform.t _ _ _ term _ term
  _ 
  eval_pir_program :=
  erasure_pipeline_mapping ▷
  east_to_stlc_transform ▷
  stlc_to_pir_transform.
Next Obligation.
(* well-formed implies translatable, needs subset condition *)
Admitted.
Next Obligation.
(* tl et = Some t -> tl t = Some et *)
Admitted.

Import Strings.String.

Axiom assume_translatable : forall p, pre simple_pipeline ([], p).

Definition compile_pir (p : Ast.Env.program) : PIR.term :=
  (run simple_pipeline ([], p) (assume_translatable p)).2.

Eval vm_compute in <# (fun (x : bool) => x) true #>.
Eval vm_compute in (run erasure_pipeline_mapping ([], <# (fun (x : bool) => x) true #>)) _.
Eval vm_compute in compile_pir <# (fun (x : bool) => x) true #>.
