From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Translation.

Existing Instance EWcbvEval.default_wcbv_flags.

(* do we need context? *)
Inductive InReflSubset (ctx : list bs) : EAst.term -> Prop :=
  | RS_tBox : InReflSubset ctx tBox
  | RS_tRel : forall n res,
    nth_error ctx n = Some res ->
    InReflSubset ctx (tRel n)
  | RS_tLambda : forall na b,
    InReflSubset ctx b ->
    InReflSubset ctx (tLambda na b)
.

Inductive InSubset (ctx : list bs) : EAst.term -> Prop :=
  | S_tBox : InSubset ctx tBox
  | S_tRel : forall n res,
    nth_error ctx n = Some res ->
    InSubset ctx (tRel n)
  | S_tLambda : forall na b,
    InSubset ctx b ->
    InSubset ctx (tLambda na b)
  | S_tApp : forall t1 t2,
    InSubset ctx t1 ->
    InSubset ctx t2 ->
    InSubset ctx (tApp t1 t2)
.

Import Coq.Strings.String.
Local Open Scope string_scope.
Import MCMonadNotation.

Notation "ctx ⊢ tl{ gt | ann_gt }" := (translate_term remap_env ctx gt ann_gt) (at level 100).
Notation "pt '⇓ₚ' pv" :=
  (evaluatesTo pt pv)
  (at level 50).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac solve_inv := intros pt pv Hgt Hgv; inversion Hgt; inversion Hgv; solve_pir_eval.
Ltac solve_err := simpl in *; try contradiction; try discriminate.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x"%bs) (tRel 0).

Theorem id_correct_explicit : forall Σ ctx pir_id, 
  let ann := (TArr (TConst <%% unit %%>) (TConst <%% unit %%>), (TConst <%% unit %%>)) in
  Σ e⊢ gal_id ⇓ gal_id ->
  (translate_term remap_env ctx gal_id ann) = Some pir_id ->
  pir_id ⇓ₚ pir_id.
Proof with (eauto using eval).
  intros Σ ctx pir_id ann ev tl.
  unfold gal_id in *. simpl in *.
  inversion tl. solve_pir_eval.
Qed.

Theorem id_correct_implicit : forall Σ ctx (ann : annots box_type gal_id) pir_id,
  Σ e⊢ gal_id ⇓ gal_id ->
  (translate_term remap_env ctx gal_id ann) = Some pir_id ->
  pir_id ⇓ₚ pir_id.
Proof with (eauto using eval).
  intros Σ ctx ann pir_id ev tl.
  unfold gal_id in *.
  destruct ann as [ty t_ty]. rewrite unfold_lamAbs in tl.
  destruct ty; try discriminate.
  destruct (translate_ty remap_env ty1);
  inversion tl; solve_pir_eval.
Qed.

(* contexts don't match in both branches! *)
Lemma tl_app : forall ctx t1 t2 ann_t (t' : PIR.term),
  translate_term remap_env ctx (tApp t1 t2) ann_t = Some t' ->
  exists ann_t1 ann_t2 t1' t2',
    translate_term remap_env ctx t1 ann_t1 = Some t1' /\
    translate_term remap_env ctx t2 ann_t2 = Some t2' /\
    Apply t1' t2' = t'.
Proof.
  intros ctx t1 t2 ann_t t' tl_a.
  inversion tl_a as [Ha].
  destruct ann_t as [ann_t [ann_t1 ann_t2]].
  destruct (translate_term remap_env ctx t1 ann_t1) as [t1'|] eqn:Et1; try discriminate.
  destruct (translate_term remap_env ctx t2 ann_t2) as [t2'|] eqn:Et2; try discriminate. 
  simpl in Ha. exists ann_t1. exists ann_t2. exists t1'. exists t2'.
  inversion Ha. auto.
Qed.
  
Theorem refl_tl_correct : forall Σ ctx gt (ann : annots box_type gt) pt,
  Σ e⊢ gt ⇓ gt ->
  InReflSubset ctx gt ->
  (translate_term remap_env ctx gt ann) = Some pt ->
  pt ⇓ₚ pt.
Proof with (eauto using eval).
  intros Σ ctx gt ann pt ev rsub tl.
  destruct rsub.
  - (* TBox *) inversion tl. solve_pir_eval.
  - (* tRel, either a translation error or ev is invalid *) 
    now inversion ev.
  - (* tLambda *) destruct ann as [ty t_ty]; try discriminate. 
    destruct na.
    + solve_err. 
    + simpl in tl. destruct ty; try discriminate.
      destruct (translate_ty remap_env ty1) as [ty1'|]; try discriminate.
      destruct (i :: ctx ⊢ tl{ b | t_ty}) as [b'|]; try discriminate.
      inversion tl. solve_pir_eval.
Qed.

(* subst lemma, or use the named variant of EAst *)
(* Print csubst. *)
Lemma tl_subst : forall ctx k x v b ann_v ann_b ann_t v' b',
  translatesTo remap_env ctx v ann_v v' ->
  translatesTo remap_env ctx b ann_b b' ->
  translatesTo remap_env ctx (csubst v k b) ann_t (BigStepPIR.subst x v' b').
Proof.
  intros ctx k x v b ann_v ann_b ann_t v' b' tlt_v tlt_b.
  inversion tlt_b.
  - simpl. subst. apply tlt_tt.
  - simpl in *. destruct (x =? (bs_to_s x0)). subst.
    simpl in *. inversion tlt_v. Admitted.


Definition id_app := tApp
  (tLambda (BasicAst.nNamed "x"%bs) (tRel 0)) (tBox).

Theorem stlc_correct : forall Σ ctx 
  gt (ann_gt : annots box_type gt) pt
  gv (ann_gv : annots box_type gv) pv,
  Σ e⊢ gt ⇓ gv ->
  InSubset ctx gt ->
  translate_term remap_env ctx gt ann_gt = Some pt ->
  InSubset ctx gv ->
  translate_term remap_env ctx gv ann_gv = Some pv ->
  pt ⇓ₚ pv.
Proof with (eauto using eval).
  intros Σ ctx gt ann_gt pt gv ann_gv pv ev sub_gt.
  revert pt pv. induction ev; try discriminate; intros pt pv.
  - simpl. destruct ann_gt. Admitted.
