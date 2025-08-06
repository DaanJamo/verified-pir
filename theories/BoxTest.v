From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Erasure.
From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import Extraction.
From Coq Require Import ZArith.
From Coq Require Import List.

Import MCMonadNotation.
Import ListNotations.

Program Definition cic_to_box p :=
  run_erase_program default_erasure_config ([], p) _.
Next Obligation.
  split. easy.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform (fun _ => None) true true false false false] |} |}.

Definition cic_to_box_typed p :=
  entry <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun k => false);;
  Ok Σ.

Check annot_extract_template_env_within_coq_sig.

(* Program Definition erase_type_of_program (p : Ast.Env.program) : P.global_env_ext * box_type :=
    let Σ := TemplateToPCUIC.trans_global_env p.1 in
    let Σext := P.empty_ext (PCUICProgram.trans_env_env Σ) in
    (Σext, erase_type_of Σext _ [] (Vector.nil _) (TemplateToPCUIC.trans Σ p.2) _).
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  MetaCoq Quote Recursively Definition eid := (fun (x : nat) => x).
  Eval cbv in (erase_type_of_program eid). *)

Definition eid := (fun (x : nat) => x).
MetaCoq Quote Recursively Definition t := eid.
Eval cbv in (t.1).

Definition kn_t : kername := (MPfile ["BoxTest"; "VTL"], "eid").

Definition kns := KernameSet.union (KernameSet.singleton kn_t) (KernameSet.singleton (MPfile ["Datatypes"; "Init"; "Coq"], "nat")).
Eval vm_compute in extract_template_env_within_coq t.1 kns (fun _ => true).

Definition get_pair_of_first_constant (env : result ExAst.global_env string) :=
  match env with
  | Ok decls => 
      match decls with
      | (((kn, deps), decl) :: _) => 
          match decl with
          | ExAst.ConstantDecl cst =>
            match cst.(ExAst.cst_body) with
            | Some t => Ok (cst.(ExAst.cst_type).2, t)
            | None => Err "constant doesn't have a body" end
          | _ => Err "not a constant" end
      | _ => Err "empty environment" end
  | _ => Err "translation failed" end.

(* Example term *)
Definition t := fun (x : nat) => x.

(* Translate Coq def -> lambda_cic/Template program *)
MetaCoq Quote Recursively Definition ex1 := t.

(* Translate lambda_cic -> lambda_box *)
Eval vm_compute in cic_to_box ex1.

(* Translate lambda_cic -> lambda_boxtyped *)
(* Note that this only translates the environment *)
(* result ExAst.globalEnv string *)
(* ExAst.globalEnv = list ((kername x bool {has_deps}) x ExAst.global_decl)*)
Eval vm_compute in cic_to_box_typed ex1.
