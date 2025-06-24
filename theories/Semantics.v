From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Subset Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.

Import Coq.Strings.String.
Import MCMonadNotation.

Notation "t' '⇓ₚ' v'" :=
  (evaluatesTo t' v')
  (at level 50).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac tl_reflect  Htl  := apply translate_reflect in Htl  as ?tlt.
Ltac tlt_reflect Htlt := apply translate_reflect in Htlt as ?tl.
Ltac invs H := inversion H; subst.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x"%bs) (tRel 0).

(* To be infered from lambda binders *)
Lemma fresh_axiom : forall (Γ : list bs) x s,
  ~ (In x Γ) ->
  ~ (In x (s :: Γ)).
Admitted.

Lemma weaken_ctx : forall Γ x t ann t',
  ~ (In x Γ) ->
  InSubset Γ t ->
  translate_term remap_env Γ t ann = Some t' ->
  translate_term remap_env (Γ ++ [x]) t ann = Some t'.
Proof.
  intros Γ x t ann t'' nIn sub. revert t''.
  induction sub; intros t' tl_t;
  tl_reflect tl_t; inversion tlt.
  - auto.
  - simpl. apply nth_error_Some_length in H.
    rewrite nth_error_app1, H2. auto. apply H.
  - (* lambda case *) admit.
  - (* app *) admit.
Admitted.

Lemma tl_closed : forall Γ t ann t',
  InSubset Γ t ->
  translate_term remap_env Γ t ann = Some t' ->
    closedn #|Γ| t /\ 
    closedUnder (map String.to_string Γ) t'.
Proof.
  intros Γ t ann t'' sub. revert t''. 
  induction sub; intros t' tl_t; tl_reflect tl_t.
  - inversion tlt. auto. 
  - split.
    + now apply nth_error_Some_length, Nat.ltb_lt in H.
    + inversion tlt. simpl. apply nth_error_In in H2.
      apply existsb_exists. exists (bs_to_s x). 
      split.
      * apply in_map. apply H2.
      * now apply eqb_eq.
  - inversion tlt. tl_reflect H4.
    specialize (IHsub ann_b b' tlt0). simpl in IHsub.
    simpl. apply IHsub.
  - inversion tlt.
    tl_reflect H1. tl_reflect H4.
    specialize (IHsub1 ann_t1 t1' tlt0).
    specialize (IHsub2 ann_t2 t2' tlt1).
    simpl. destruct IHsub1, IHsub2. 
    auto.
Qed.

Lemma tl_subst : forall Γ k x v b ann_v ann_b ann_t v' b',
  nth_error Γ k = Some x ->
  translatesTo remap_env nil v ann_v v' ->
  translatesTo remap_env (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Γ (csubst v k b) ann_t (BigStepPIR.subst (bs_to_s x) v' b').
Proof.
  intros Γ k x v b ann_v ann_b ann_t v' b'. revert Γ k ann_t b'.
  induction b; intros Γ k' ann_t b' inCtx tlt_v tlt_b; inversion tlt_b.
  - simpl. apply tlt_tt.
  - simpl in *. admit.
  - destruct ann_t as [ty ann_sb].
    (* lambda case, annotations need to have the right form *)
    admit.
  - simpl in *. subst.
    destruct ann_t as [t_ty [ann_st1 ann_st2]].
    specialize (IHb1 ann_t1 Γ k' ann_st1 t1' inCtx tlt_v H1).
    specialize (IHb2 ann_t2 Γ k' ann_st2 t2' inCtx tlt_v H4).
    apply (tlt_app remap_env Γ). apply IHb1. apply IHb2.
Admitted.

Theorem stlc_correct : forall Γ 
  t (ann_t : annots box_type t) t'
  v (ann_v : annots box_type v),
  [] e⊢ t ⇓ v ->
  InSubset Γ t ->
  InSubset Γ v ->
  translatesTo remap_env Γ t ann_t t' ->
  exists ann_v v' k,
    translatesTo remap_env Γ v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros Γ t ann_t t' v ann_v ev. revert t'.
  induction ev; intros t'' sub_t sub_v tlt_t;
  inversion sub_t.
  - admit. (* nonsensible case right now *)
  - (* apply, the sensible case which requires subst-lemma *) admit.
  - (* mkApps case *) subst. invs tlt_t. admit.
  - (* fix case *) subst. inversion sub_v. 
    apply mkApps_in_subset in H3 as [Hcontra _].
    inversion Hcontra.
  - (* fix case *) inversion tlt_t. subst. admit.
  - (* mkApps constr case *) subst. inversion tlt_t. subst.
    admit.
  - (* Atoms applied to values *) admit.
  (* Atoms *)
  - subst. inversion tlt_t. exists ann. exists t''.
    subst. eexists. split. apply tlt_tt. apply E_Constant. eauto.
  - subst. inversion i.
  - subst. exists ann_t. exists t''. inversion tlt_t. 
    subst. eexists. split. apply tlt_t. apply E_LamAbs. eauto.
Admitted.
