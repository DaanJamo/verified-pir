From Coq Require Import Program.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Erasure Require Import ExAst EProgram EWcbvEval.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations Utils.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Template Require Import Loader TemplateMonad.
From MetaCoq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.

From VTL Require PIR BigStepPIR.
From VTL Require Import Translation.

(* Verified PIR extraction: Gallina ▷ PCUIC ▷ λ□T ▷ PIR *)

From Coq.Strings Require Import String.
Import MCMonadNotation ListNotations.

Local Existing Instance extraction_checker_flags.

Definition gal_id := fun x : nat => x.

Definition plus_one n : nat := n + 1.

Import Common.Transform.Transform.

#[local] Obligation Tactic := program_simpl.

Definition pir_fuel := 5000.
Definition pir_program := (unit * PIR.term).
Definition eval_pir_program (p' : pir_program) (t' : PIR.term) :=
  BigStepPIR.eval p'.2 t' 5000.

Definition prog  : eprogram := ([], EAst.tBox).
Definition prog' : pir_program := (tt, PIR.Var "x"%string).

Definition always  (p  : eprogram)    : Prop := True.
Definition always' (p' : pir_program) : Prop := True.
Definition trust (p : eprogram) (pre : always p) := True.

Definition nom (p : eprogram) : always p -> pir_program := fun _ => (tt, PIR.Var "x"%string).

(* Record
t (env env' term term' value value' : Type) (eval : program env term -> value -> Prop)
(eval' : program env' term' -> value' -> Prop) : Type := Build_t
  { name : bytestring.string;  pre : program env term -> Prop;
  transform : forall p : program env term, pre p -> program env' term';
  post : program env' term' -> Prop;
  correctness : forall (input : program env term) (p : pre input), post (transform input p);
  obseq : forall p : program env term, pre p -> program env' term' -> value -> value' -> Prop;
  preservation : preserves_eval pre transform obseq }. *)

Program Definition box_to_pir_transform_test : 
  Transform.t global_context unit EAst.term PIR.term EAst.term PIR.term
  (eval_eprogram default_wcbv_flags)
  (eval_pir_program) := 
  {| name := "translate lambda box terms into PIR terms";
     pre p := always p;
     transform p pre := nom p pre;
     post p' := always' p';
     correctness p pre := _;
     obseq p Hp p' _ _ := _;
     preservation := _
  |}.
Next Obligation.
  unfold always in Hp. Admitted.
Next Obligation.
  Admitted.

Definition run_transform (t : EAst.term) :=
  run box_to_pir_transform_test ([], t).

Eval cbv in (run_transform EAst.tBox I).

Definition template_to_lt (t : Ast.term) : TemplateMonad (∑ et : EAst.term, annots box_type et) :=
  match t with
  | Ast.tConst _ _ => ret (existT (annots box_type) identity_EAst (TArr (TConst <%% bool %%>) (TConst <%% bool %%>), (TConst <%% bool %%>)))
  | _ => ret (existT (annots box_type) identity_EAst ann_id)
  end.

Definition compile_pir (t : Ast.term) : TemplateMonad PIR.term :=
  p <- template_to_lt t ;;
  match p with | existT et ann =>
    match translate_term remap_env [] et ann with
    | Some t' => ret t'
    | _ => ret (PIR.Error (PIR.UNDEFINED "Not Implemented"))
    end
  end.

(* Check run (typed_erasure_pipeline typed_erasure_config [] ([], )). *)
MetaCoq Run (tmQuote gal_id >>= compile_pir >>= tmEval cbn >>= tmPrint).

MetaCoq Erase -typed gal_id.
