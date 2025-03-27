From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Universes Kernames.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.
From MetaCoq.Erasure.Typed Require Import ExAst Utils TypeAnnotations.

From VTL Require Import PIR Translation.

Import MCMonadNotation.

(* 
Check ErasureFunction.erase.
MetaCoq Erase -help.
MetaCoq Erase -typed e.
*)

Import PCUICAst.
Definition annot_extract_env_pir
           (Σ : PCUICEnvironment.global_env)
           (wfΣ : ∥wf Σ∥)
           (include : KernameSet.t)
           (ignore : list kername) : result (∑ Σ, env_annots box_type Σ) string.
Proof.



Program Definition annot_extract_template_env_specialize
          (e : Ast.Env.global_env)
          (seeds : KernameSet.t)
          (ignore : list kername) : result_string (∑ e, env_annots box_type e) :=
let pEnv := TemplateToPCUIC.trans_global_env e in
conf <- check_wf_env_func extract_within_coq ;;
(* e <- specialize_ChainBase_env (PCUICProgram.trans_env_env e) ;;
wfe <-check_wf_env_func extract_within_coq e;;
annot_extract_env_cameligo e wfe seeds ignore. *)


Definition preprocess_def {A} (def : A) 
  : TemplateMonad (Ast.Env.global_env * kername) :=
  '(Σ,_) <- tmQuoteRecTransp def false ;;
  def_nm <- extract_def_name def ;;
  decls <- ret (Ast.Env.declarations Σ) ;;
  Σret <- tmEval lazy 
    (Ast.Env.mk_global_env (ContextSet.empty) decls (Ast.Env.retroknowledge Σ)) ;;
  ret (Σret, def_nm).

(* declare a definition with MetaCoq *)
Open Scope bs_scope.
Definition faif := 5.
MetaCoq Run (preprocess_def faif >>= fun '(_, df) => tmDefinition (df.2 ++ "_plusOne") 6).
Print faif_plusOne.

(*def_nm.2 = ident*)
Definition extract_single (def : A) : TemplateMonad PIR.term :=
  '(Σ,def_nm) <- preprocess_def inline def ;;
  let seeds := KernameSetProp.of_list [def_nm] in
  tmDefinition (def_nm.2 ++ "_prepared") 


