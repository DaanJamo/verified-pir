From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Loader.
From VTL Require Import PIR BigStepPIR Translation.

Existing Instance EWcbvEval.default_wcbv_flags.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x") (tVar "x").

Lemma galEvalId : forall Σ, Σ e⊢ gal_id ⇓ gal_id.
Proof.
  intros. eauto.
Qed.

Theorem id_correct : forall Σ, Σ e⊢ gal_id ⇓ gal_id ->
  ((translate_term remap_env gal_id) ann_id) ⇓ ((translate_term remap_env gal_id) ann_id).
Proof with (eauto using eval).
  intros.
  unfold gal_id in *.
  simpl in *. split.
  - eexists...
  - constructor.
Qed.

Theorem translation_correct : 
  forall Σ gt (ann : annots box_type gt),
  Σ e⊢ gt ⇓ gt ->
  (* InSubset gt -> *)
  (translate_term remap_env gt ann) ⇓ (translate_term remap_env gt ann).
Proof.
  intros.
  induction H.
  (* discriminate using InSubset gt *)
Admitted.
