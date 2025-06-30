From MetaCoq.Erasure Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations Utils.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Template Require Import Loader TemplateMonad.
From MetaCoq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaCoq.Utils Require Import utils.
Import config.

From VTL Require Import PIR Translation.

From Coq.Strings Require Import String.
Import MCMonadNotation ListNotations.

Local Existing Instance extraction_checker_flags.

Definition gal_id := fun x : nat => x.

Definition plus_one n : nat := n + 1.

(* empty_ext empty_global_env *)
MetaCoq Quote Recursively Definition gid := 3.
Eval cbv in run_erase_program typed_erasure_config  gid.

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

(* MetaCoq Run ((tmQuoteRec 3) >>= tmEval cbv >>= tmPrint).
MetaCoq Quote Recursively Definition gid := gal_id.
Eval cbv in (gid.2). *)

MetaCoq Run (tmQuote gal_id >>= compile_pir >>= tmEval cbn >>= tmPrint).
