From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Loader.
From VTL Require Import PIR BigStepPIR Translation.

Existing Instance EWcbvEval.default_wcbv_flags.

Definition InSubset gt :=
  match gt with
  | tRel _
  | tLambda _ _
  | tApp (tLambda _ _) _ => True
(* | some primitive value to replace vars with *)
  | _ => False
  end.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x") (tRel 0).

Import Coq.Strings.String.
Local Open Scope string_scope.

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac solve_err := simpl in *; contradiction.

Lemma galEvalId : forall Σ, Σ e⊢ gal_id ⇓ gal_id.
Proof.
  intros. eauto.
Qed.

Theorem id_correct_explicit : forall Σ, Σ e⊢ gal_id ⇓ gal_id ->
  let gal_id' := (translate_term remap_env nil gal_id
    (TArr (TConst <%% unit %%>) (TConst <%% unit %%>), (TConst <%% unit %%>))) in
  gal_id' ⇓ gal_id'.
Proof with (eauto using eval).
  intros.
  unfold gal_id' in *.
  simpl in *. split... constructor.
Qed.

Theorem id_correct_implicit : forall Σ ctx (ann : annots box_type gal_id),
  let gal_id' := translate_term remap_env ctx gal_id ann in
  Σ e⊢ gal_id ⇓ gal_id ->
  InSubset gal_id ->
  ~ (isError gal_id') ->
  gal_id' ⇓ gal_id'.
Proof with (eauto using eval).
  intros. simpl in gal_id'.
  destruct ann eqn:Ea. destruct (decompose_arr b).
  destruct l; try solve_err; 
  unfold get_type in gal_id';
  try solve_pir_eval;
  try solve_err.
  induction b1;
  try solve_pir_eval;
  try solve_err.
  destruct (Env.with_default (UNDEFINED "NotInMap")
  (Env.lookup remap_env
  (bs_to_s Kernames.string_of_kername k)));
  try solve_pir_eval;
  try solve_err.
Qed.

Theorem trans_lambda : forall ctx na t bt1 bt2 (ann : annots box_type t),
  let lt := translate_term remap_env ctx (tLambda na t) (TArr bt1 bt2, ann) in
  ~ (isError lt) ->
  lt ⇓ lt.
Proof with (eauto using eval).
  intros.
  simpl in lt. destruct (decompose_arr bt2).
  - induction bt1; unfold get_type in lt;
  try solve_pir_eval;
  try solve_err.
  (* this is fragile*)
  destruct (Env.with_default (UNDEFINED "NotInMap")
  (Env.lookup remap_env
  (bs_to_s Kernames.string_of_kername k)));
  try solve_pir_eval;
  try solve_err.
Qed.

Theorem translation_correct : 
  forall Σ ctx gt (ann : annots box_type gt),
  let gt' := translate_term remap_env ctx gt ann in
  Σ e⊢ gt ⇓ gt ->
  InSubset gt ->
  ~ isError gt' ->
  gt' ⇓ gt'.
Proof with (eauto using eval).
  intros Σ ctx gt ann gt' ev sub nerr. 
  destruct gt eqn:Egt; simpl in gt';
  (* this gets rid of terms that are not implemented or give a trivial error *)
  try solve_err.
  (* - (* tBox => Constant, add this if tBox is in the subset *) try solve_pir_eval. *)
  - (* tRel *) destruct (nth_error ctx n).
    + destruct c. destruct decl_name.
      * solve_err.
      * split.
        ** eexists. unfold gt'. admit. (* what to do in var case *)
        ** unfold gt'. admit.
    + solve_err.
  - (* tLambda *) destruct ann eqn:Ea. destruct b; simpl in gt';
    try solve_err.
    + apply trans_lambda. simpl. destruct (decompose_arr b2).
      destruct (get_type remap_env b1)...
  - (*tApp*) destruct t1; simpl in sub; try contradiction.
    (* lemma that is valid for all types that make sense *)
    simpl in *. admit.
Admitted.
