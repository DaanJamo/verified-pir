From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Subset Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.
Set Default Goal Selector "!".

Import Coq.Strings.String.
Import Coq.Logic.Eqdep.
Import MCMonadNotation.

Notation "t' '⇓ₚ' v'" :=
  (evaluatesTo t' v')
  (at level 50).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac tl_reflect Htl := apply translate_reflect in Htl as ?tlt.
Ltac invs H := inversion H; subst.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x"%bs) (tRel 0).

Lemma weaken_ctx : forall Γ x t ann t',
  translatesTo remap_env Γ t ann t' ->
  translatesTo remap_env (Γ ++ [x]) t ann t'.
Proof.
  intros Γ x t. revert Γ.
  induction t; intros Γ ann t' tlt;
  inversion tlt; subst.
  - constructor.
  - apply tlt_rel. now apply find_index_weaken.
  - apply inj_pair2 in H2. subst.
    apply tlt_lambda. 
    + assumption.
    + now apply (IHt (x' :: Γ)).
  - apply inj_pair2 in H2. subst. 
    apply tlt_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Lemma weaken_ctx_many : forall Γ1 Γ2 t ann t',
  translatesTo remap_env Γ1 t ann t' ->
  translatesTo remap_env (Γ1 ++ Γ2) t ann t'.
Proof.
  intros Γ1 Γ2 t. revert Γ1. induction t;
  intros Γ1 ann t' tlt_t; 
  inversion tlt_t; subst.
  - constructor.
  - apply tlt_rel. now apply find_index_weaken.
  - apply inj_pair2 in H2. subst.
    apply tlt_lambda. 
    + assumption.
    + now apply (IHt (x' :: Γ1)).
  - apply inj_pair2 in H2. subst.
    apply tlt_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Lemma strengthen_shadowed_ctx : forall Γ x b ann_b b',
  In x Γ ->
  translatesTo remap_env (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Γ b ann_b b'.
Proof.
  intros Γ x b. revert Γ. induction b;
  intros Γ ann_b b' Hin tlt; inversion tlt; subst.
  - constructor.
  - apply tlt_rel.
    unfold find_index_string in H1.
    destruct_str_eq x x0.
    + subst. now rewrite find_index_app1 in H1.
    + rewrite find_index_app1 in H1; auto.
      now eapply find_index_not_outer.
  - apply inj_pair2 in H2. subst.
    apply tlt_lambda. 
    + assumption.
    + apply IHb.
      * now right. 
      * assumption.
  - apply inj_pair2 in H2. subst.
    apply tlt_app.
    + apply IHb1; assumption.
    + apply IHb2; assumption.
Qed.

Definition annot_csubst {v} (ann_v : annots box_type v) :
  forall k {b} (ann_b : annots box_type b), annots box_type (csubst v k b).
Proof.
  fix f 2.
  intros k t ann_b.
  destruct t eqn:Et; cbn in *; try exact ann_b.
  - destruct (_ ?= _).
    * exact ann_v.
    * exact ann_b.
    * exact ann_b.
  - refine (ann_b.1, bigprod_map _ ann_b.2).
    apply f.
  - exact (ann_b.1, f _ _ ann_b.2).
  - exact (ann_b.1, (f _ _ ann_b.2.1, f _ _ ann_b.2.2)).
  - exact (ann_b.1, (f _ _ ann_b.2.1, f _ _ ann_b.2.2)).
  - refine (ann_b.1, (f _ _ ann_b.2.1, bigprod_map _ ann_b.2.2)).
    intros.
    exact (f _ _ X).
  - exact (ann_b.1, f _ _ ann_b.2).
  - refine (ann_b.1, bigprod_map _ ann_b.2).
    intros.
    exact (f _ _ X).
  - refine (ann_b.1, bigprod_map _ ann_b.2).
    intros.
    exact (f _ _ X).
Defined.

Lemma csubst_shadowed : forall Γ x b ann_b b' v ann_v,
  In x Γ ->
  translatesTo remap_env (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env (Γ ++ [x]) (csubst v (List.length Γ) b) (annot_csubst ann_v (List.length Γ) ann_b) b'.
Proof.
  intros Γ x b. revert Γ. induction b; 
  intros Γ ann_b b' v ann_v Hin tlt; inversion tlt.
  - constructor.
  - simpl. unfold find_index_string in H1.
    destruct (#|Γ| ?= n) eqn:Hc.
    + apply Nat.compare_eq_iff in Hc as Hl.
      subst. apply find_index_outer in H1 as Hx.
      subst x. now apply find_index_outer_not_In in H1.
    + apply find_index_Some_length in H1 as Hl.
      apply Nat.compare_lt_iff in Hc.
      rewrite last_length in Hl. lia.
    + now apply tlt_rel.
  - apply inj_pair2 in H2. subst.
    specialize (IHb (x' :: Γ) ann_b0 b'0 v).
    simpl in *. apply tlt_lambda; auto.
  - apply inj_pair2 in H2. subst. 
    simpl. apply tlt_app.
    + apply IHb1; auto.
    + apply IHb2; auto.
Qed.

Lemma csubst_correct : forall Γ x v b ann_v ann_b v' b',
  ~ In x Γ ->
  translatesTo remap_env nil v ann_v v' ->
  translatesTo remap_env (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Γ (csubst v (List.length Γ) b)
  (annot_csubst ann_v (List.length Γ) ann_b)
  (BigStepPIR.subst x v' b').
Proof.
  intros Γ x v b. revert Γ. induction b;
  intros Γ ann_v ann_b v' b' HnIn tlt_v tlt_b;
  inversion tlt_b; subst.
  - constructor.
  - destruct_str_eq x x0; subst.
    + apply find_index_outer_length in H1 as Hl; auto.
      symmetry in Hl. apply Nat.compare_eq_iff in Hl.
      simpl in *. rewrite eqb_refl, Hl.
      now eapply weaken_ctx_many in tlt_v.
    + apply find_index_not_outer in H1 as Hin; auto.
      apply find_index_not_outer_length in H1 as Hl; auto.
      unfold find_index_string in H1.
      rewrite find_index_app1 in H1; auto.
      simpl in *. destruct (#|Γ| ?= n) eqn:Hc.
      * now apply Nat.compare_eq_iff, Nat.eqb_eq in Hc.
      * apply find_index_Some_length in H1 as Hn.
        now apply Nat.compare_lt_iff in Hc.
      * rewrite Heqb. now apply tlt_rel.
  - apply inj_pair2 in H2. subst.
    simpl. destruct_str_eq x x'.
    + apply tlt_lambda. 
      * assumption.
      * subst x'. assert (Hin : In x (x::Γ)) by now left.
        specialize (csubst_shadowed (x :: Γ) x b ann_b0 b'0 v ann_v Hin H4).
        intros. simpl in H.
        specialize (strengthen_shadowed_ctx (x :: Γ) x (csubst v (S #|Γ|) b) (annot_csubst ann_v (S #|Γ|) ann_b0) b'0 Hin H) as Hctx'.
        apply Hctx'.
    + apply tlt_lambda.
      * assumption.
      * apply IHb; auto. now apply not_in_cons.
  - apply inj_pair2 in H2. subst.
    specialize (IHb1 Γ ann_v ann_t1 v' t1' HnIn tlt_v H1).
    specialize (IHb2 Γ ann_v ann_t2 v' t2' HnIn tlt_v H4).
    now apply tlt_app.
Qed.

Theorem stlc_correct : forall
  t (ann_t : annots box_type t) t'
  v (ann_v : annots box_type v),
  [] e⊢ t ⇓ v ->
  InSubset [] t ->
  InSubset [] v ->
  translate_term remap_env [] t ann_t = Some t' ->
  exists ann_v v' k,
    translatesTo remap_env [] v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros t ann_t t' v ann_v ev sub_t sub_v tlt.
  apply translate_reflect in tlt; try apply NoDup_nil. 
  revert t' tlt; induction ev; 
  intros t'' tlt; inversion sub_t.
  - admit. (* nonsensible case right now *)
  - (* apply case *) admit.
  - (* mkApps case *) subst. invs tlt. admit.
  - (* fix case *) subst. inversion sub_v. 
    apply mkApps_in_subset in H3 as [Hcontra _].
    inversion Hcontra.
  - (* fix case *) inversion tlt. subst. admit.
  - (* mkApps constr case *) subst. inversion tlt. subst.
    admit.
  - (* Atoms applied to values *) admit.
  (* Atoms *)
  - subst. inversion tlt. exists ann. exists t''.
    subst. eexists. split. 
    + apply tlt_tt. 
    + apply E_Constant. eauto.
  - subst. inversion i.
  - subst. exists ann_t. exists t''. inversion tlt. 
    subst. eexists. split. 
    + apply tlt. 
    + apply E_LamAbs. eauto.
Admitted.
