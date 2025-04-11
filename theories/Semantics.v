From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Translation.

Existing Instance EWcbvEval.default_wcbv_flags.

Inductive InReflSubset (ctx : context) : EAst.term -> Prop :=
  | RS_tBox : InReflSubset ctx tBox
  | RS_tRel : forall n res,
    nth_error ctx n = Some res ->
    InReflSubset ctx (tRel n)
  | RS_tLambda : forall na t,
    InReflSubset ctx t ->
    InReflSubset ctx (tLambda na t)
.

Inductive InSubset (ctx : context) : EAst.term -> Prop :=
  | S_tBox : InSubset ctx tBox
  | S_tRel : forall n res,
    nth_error ctx n = Some res ->
    InSubset ctx (tRel n)
  | S_tLambda : forall na t,
    InSubset ctx t ->
    InSubset ctx (tLambda na t)
  | S_tApp : forall t1 t2,
    InSubset ctx t1 ->
    InSubset ctx t2 ->
    InSubset ctx (tApp t1 t2)
.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x") (tRel 0).

Import Coq.Strings.String.
Local Open Scope string_scope.

Notation "ctx p⊢ tl{ gt | ann_gt }" := (translate_term remap_env ctx gt ann_gt) (at level 100).
Notation "ctx p⊢ { gt | ann_gt } '⇓ₚ' { gv | ann_gv }" :=
  (forall pt pv,
  (translate_term remap_env ctx gt ann_gt) = Some pt ->
  (translate_term remap_env ctx gv ann_gv) = Some pv ->
  (evaluatesTo pt pv))
  (at level 50, gt, ann_gt, gv, ann_gv at next level).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac solve_inv_eval := intros pt pv Hgt Hgv; inversion Hgt; inversion Hgv; solve_pir_eval.
Ltac solve_err := simpl in *; try contradiction; try discriminate.

Lemma galEvalId : forall Σ, Σ e⊢ gal_id ⇓ gal_id.
Proof.
  intros. eauto.
Qed.

Theorem id_correct_explicit : forall Σ, 
  let ann := (TArr (TConst <%% unit %%>) (TConst <%% unit %%>), (TConst <%% unit %%>)) in
  Σ e⊢ gal_id ⇓ gal_id ->
  nil p⊢ {gal_id | ann} ⇓ₚ {gal_id | ann}.
Proof with (eauto using eval).
  intros Σ ann ev.
  unfold gal_id in *. simpl in *.
  solve_inv_eval.
Qed.

Theorem id_correct_implicit : forall Σ ctx (ann : annots box_type gal_id),
  Σ e⊢ gal_id ⇓ gal_id ->
  InSubset ctx gal_id ->
  ctx p⊢ { gal_id | ann } ⇓ₚ { gal_id | ann }.
Proof with (eauto using eval).
  intros Σ ctx ann ev sub.
  unfold gal_id in *.
  destruct ann as [bt a]. rewrite unfold_lamAbs.
  destruct (decompose_arr bt) as [[] _]; try discriminate.
  destruct (get_type remap_env b). simpl.
  - solve_inv_eval.
  - discriminate.
Qed.

Theorem tl_lambda : forall ctx na t (ann : annots box_type (tLambda na t)),
  ctx p⊢ { tLambda na t | ann} ⇓ₚ { tLambda na t | ann}.
Proof with (eauto using eval).
  intros ctx na t ann.
  destruct ann as [bt a]. rewrite unfold_lamAbs.
  destruct (decompose_arr bt) as [[] _]; try discriminate.
  destruct (get_type remap_env b) as [ty|]; try discriminate.
  destruct t; try discriminate; simpl.
  - solve_inv_eval.
  - destruct (nth_error (vass (BasicAst.nNamed (s_to_bs get_name na)) :: ctx) n).
    destruct c. destruct decl_name; try discriminate. simpl.
    + solve_inv_eval.
    + discriminate.
  - destruct a as [[] a']; try discriminate.
    + simpl. destruct (decompose_arr codom).
    destruct (get_type remap_env dom) as [ty'|]; try discriminate. admit.
  - admit.
Admitted.

(* use unfold lemmas, translate app = *)
Theorem refl_tl_correct : forall Σ ctx gt (ann : annots box_type gt),
  Σ e⊢ gt ⇓ gt ->
  InReflSubset ctx gt ->
  ctx p⊢ { gt | ann} ⇓ₚ {gt | ann}.
Proof with (eauto using eval).
  intros Σ ctx gt ann ev rsub.
  destruct rsub.
  - (* TBox *) solve_inv_eval.
  - (* tRel, either an error or ev is invalid *) 
    simpl in *. destruct (nth_error ctx n). destruct c. destruct decl_name.
    + discriminate.
    + now inversion ev.
    + discriminate.
  - (* tLambda *) destruct ann as [bt a]. rewrite unfold_lamAbs.
  destruct (decompose_arr bt). destruct l; try discriminate.
  destruct (get_type remap_env b0) as [ty|]; try discriminate.
  destruct ty eqn:Ety; simpl; try discriminate. admit.
Qed.

(*Definition id_app := tApp
  (tLambda (BasicAst.nNamed "x"%bs) (tRel 0)) (tBox).

Theorem id_app_correct : forall ctx (ann : annots box_type id_app),
  ~ (ctx p⊢ tl_err{id_app | ann}) ->
  ctx p⊢ {id_app | ann} ⇓ₚ {tBox | TBox}.
Proof with (eauto using eval).
  intros ctx ann nerr.
  unfold id_app. destruct ann. destruct p. rewrite unfold_app. split.
  - eexists. eapply E_Apply... 
  (* destruct ann as [annv [[dom codom] bt]]; try solve_err.
  destruct (decompose_arr dom); destruct l; try solve_err.
  unfold not in nerr. simpl in nerr. destruct nerr. left. trivial.
  destruct (get_type remap_env b0); split. 
  - eexists. eapply E_Apply... simpl...
  - constructor.
  - eexists. admit. (* it sees λ(x : tt, x) x as valid*)
  - constructor.
  - unfold not in nerr. simpl in nerr. destruct nerr. left. trivial.
  - constructor. *)
Admitted.

Theorem stlc_correct : forall Σ ctx 
  gt (ann_gt : annots box_type gt)
  gv (ann_gv : annots box_type gv),
  Σ e⊢ gt ⇓ gv ->
  InSubset ctx gt ->
  ~ (ctx p⊢ tl_err{gt | ann_gt}) ->
  InSubset ctx gv ->
  ~ (ctx p⊢ tl_err{gv | ann_gv}) ->
  ctx p⊢ {gt | ann_gt} ⇓ₚ {gv | ann_gv}.
Proof with (eauto using eval).
  intros Σ ctx gt ann_gt gv ann_gv.
  intros ev sub_gt nerr_gt sub_gv nerr_gv.
  (* main proof, set up useful lemmas first *)
  (* refl cases*)
Admitted. *)
