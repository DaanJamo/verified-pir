From Coq Require Import Program.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Kernames Transform config.
From MetaCoq.Template Require Import Ast Loader TemplateMonad.
From MetaCoq.Erasure Require Import ExAst EProgram EWcbvEval.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations Utils.
From MetaCoq.Erasure.Typed Require Import Extraction ResultMonad Optimize.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.

From VTL Require PIR BigStepPIR.
From VTL Require Import Translation Subset.

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
Definition eval_pir_program (p : pir_program) (v' : PIR.term) := ∥ exists k, BigStepPIR.eval p.2 v' k ∥.

(* add lemma sub => exists t', tl t = Some t'*)
Definition translate_program (p : eprogram) (sub : InSubset [] p.2) := 
  fun ann => let t' := 
    match translate_term remap_env [] p.2 ann with
    | Some t'' => t''
    | None => PIR.Error (PIR.UNDEFINED "not in subset")
    end in
  (tt, t').

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition p := (fun (x : nat) => x).
MetaCoq Quote Recursively Definition qp := p.
Eval cbv in <%% p %%>.

Import bytestring.
Locate string.
Definition cic_to_box_typed (p : Ast.Env.program) :=
  entry <- match p.2 with
           | _ => Ok <%% t %%>
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  Ok Σ.

Definition get_type_env (p : Ast.Env.program) : result ExAst.global_env string :=
  entry <- match p.2 with
           | Ast.tConst kn _ => Ok kn
           | Ast.tInd ind _ => Ok (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- annot_extract_template_env no_check_args p.1 (KernameSet.singleton entry) (fun kn => false);;
  Ok Σ.

(* Record
t (env env' term term' value value' : Type) (eval : program env term -> value -> Prop)
(eval' : program env' term' -> value' -> Prop) : Type := Build_t
  { name : bytestring.string;  pre : program env term -> Prop;
  transform : forall p : program env term, pre p -> program env' term';
  post : program env' term' -> Prop;
  correctness : forall (input : program env term) (p : pre input), post (transform input p);
  obseq : forall p : program env term, pre p -> program env' term' -> value -> value' -> Prop;
  preservation : preserves_eval pre transform obseq }. *)

Print global_context.
Program Definition east_to_pir_transform_test : 
  Transform.t global_context unit EAst.term PIR.term EAst.term PIR.term
  (eval_eprogram default_wcbv_flags)
  (eval_pir_program) := 
  {| name := "translate lambda box terms into PIR terms";
     pre p := InSubset [] p.2;
     transform p pre := translate_program p pre _;
     post _ := True;
     correctness p pre := I;
     obseq p Hp p' v v' := translatesTo remap_env [] v _ v';
     preservation := _
  |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Eval vm_compute in run (east_to_pir_transform_test (tt, identity_EAst) _).
MetaCoq Quote Recursively Definition p := bool.

(* Locate Optimize.dearg_transform.
Print extract_template_env_params.
Definition template_env_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [Optimize.dearg_transform (fun _ => None) true true false false false] |} |}.
Eval cbv in to_kername p.2.

Definition cic_to_box_typed (p : Ast.Env.program) :=
  entry <- match p.2 with
           | Ast.tConst kn _ => Ok kn
           | Ast.tInd ind _ => Ok (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         template_env_args
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  Ok Σ. *)

(* Locate canonical_abstract_env_impl.
Definition erase_type_impl (Σ : Ast.Env.global_env_ext) (wfextΣ : ∥ Typing.wf_ext Σ∥) :=
  @Erasure.erase_type PCUICWfEnvImpl.canonical_abstract_env_impl (ltac:(now unshelve econstructor;eauto)).

Locate erase_type_impl.
Program Definition erase_type_program (p : Ast.Env.program) : Ast.Env.global_env_ext * (list BasicAst.name * box_type) :=
  let Σ := TemplateToPCUIC.trans_global_env p.1 in
  let Σext := Ast.Env.empty_ext (PCUICProgram.trans_env_env Σ) in
  (Σext, erase_type_impl Σext _ Σext eq_refl (trans Σ p.2) _).
Next Obligation. Admitted.
Next Obligation. Admitted. *)

Definition run_transform (t : EAst.term) :=
  run east_to_pir_transform_test ([], t).

(* Eval vm_compute in (run_transform EAst.tBox _). *)
Eval vm_compute in (run (typed_erasure_pipeline typed_erasure_config) ([], <# 3 #>) _).

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
(* MetaCoq Run (tmQuote gal_id >>= compile_pir >>= tmEval cbn >>= tmPrint). *)
