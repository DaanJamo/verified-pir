From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.

Inductive InReflSubset (Γ : list bs) : EAst.term -> Prop :=
  | RS_tBox : InReflSubset Γ tBox
  | RS_tRel : forall n res,
    nth_error Γ n = Some res ->
    InReflSubset Γ (tRel n)
  | RS_tLambda : forall na b,
    InReflSubset Γ b ->
    InReflSubset Γ (tLambda na b)
.

Inductive InSubset (Γ : list bs) : EAst.term -> Prop :=
  | S_tBox : InSubset Γ tBox
  | S_tRel : forall n res,
    nth_error Γ n = Some res ->
    InSubset Γ (tRel n)
  | S_tLambda : forall x b,
    InSubset (x :: Γ) b ->
    InSubset Γ (tLambda (BasicAst.nNamed x) b)
  | S_tApp : forall f a,
    InSubset Γ f ->
    InSubset Γ a ->
    InSubset Γ (tApp f a)
.

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

Theorem id_correct_explicit : forall Σ Γ pir_id, 
  let ann := (TArr (TConst <%% unit %%>) (TConst <%% unit %%>), (TConst <%% unit %%>)) in
  Σ e⊢ gal_id ⇓ gal_id ->
  (translate_term remap_env Γ gal_id ann) = Some pir_id ->
  pir_id ⇓ₚ pir_id.
Proof with (eauto using eval).
  intros Σ Γ pir_id ann ev tl.
  unfold gal_id in *. simpl in *.
  inversion tl. solve_pir_eval.
Qed.

Theorem id_correct_implicit : forall Σ Γ (ann : annots box_type gal_id) pir_id,
  Σ e⊢ gal_id ⇓ gal_id ->
  (translate_term remap_env Γ gal_id ann) = Some pir_id ->
  pir_id ⇓ₚ pir_id.
Proof with (eauto using eval).
  intros Σ Γ ann pir_id ev tl.
  tl_reflect tl.
  inversion tlt. solve_pir_eval.
Qed.

Theorem refl_tl_correct : forall Σ Γ t (ann : annots box_type t) t',
  Σ e⊢ t ⇓ t ->
  InReflSubset Γ t ->
  (translate_term remap_env Γ t ann) = Some t' ->
  t' ⇓ₚ t'.
Proof with (eauto using eval).
  intros Σ Γ t ann t' ev rsub tl.
  destruct rsub.
  - (* TBox *) inversion tl. solve_pir_eval.
  - (* tRel, either a translation error or ev is invalid *) 
    now inversion ev.
  - (* tLambda *) tl_reflect tl. 
    inversion tlt. solve_pir_eval.
Qed.

Lemma mkApps_in_subset : forall Γ us f,
  InSubset Γ (mkApps f us) ->
  InSubset Γ f /\ (forall a, In a us -> InSubset Γ a).
Proof.
  intros Γ us. induction us.
  - intros. simpl in *. auto.
  - intros. simpl in H. specialize (IHus (tApp f a)).
    apply IHus in H. destruct H as [Hf Hus]. 
    inversion Hf. split.
    + assumption.
    + subst. intros a' Hin.
      inversion Hin; subst. 
      * assumption.
      * apply Hus. assumption.
Qed.

Lemma subset_closed : forall Γ t,
  InSubset Γ t ->
  closedn #|Γ| t.
Proof.
  intros Γ t' sub. induction sub.
  - reflexivity.
  - now apply nth_error_Some_length, Nat.ltb_lt in H.
  - auto.
  - simpl. auto.
Qed.

Lemma subset_weaken : forall Γ x t,
  InSubset Γ t ->
  InSubset (Γ ++ [x]) t.
Proof.
  intros Γ x t sub. induction sub.
  - constructor.
  - apply (S_tRel (Γ ++ [x]) n res). 
    apply nth_error_Some_length in H as Hl.
    rewrite (nth_error_app1 Γ [x] Hl). assumption.
  - constructor. apply IHsub.
  - constructor; assumption.
Qed.

Lemma subset_weaken_many : forall Γ1 Γ2 t,
  InSubset Γ1 t ->
  InSubset (Γ1 ++ Γ2) t.
Proof.
  intros Γ1 Γ2 t sub. induction sub.
  - constructor.
  - apply (S_tRel (Γ ++ Γ2) n res). 
    apply nth_error_Some_length in H as Hl.
    rewrite (nth_error_app1 Γ Γ2 Hl). assumption.
  - constructor. apply IHsub.
  - constructor; assumption.
Qed.

Lemma csubst_in_sub : forall (Γ1 Γ2 : list bs) x v b,
  InSubset [] v ->
  InSubset (Γ1 ++ x :: Γ2) b ->
  InSubset (Γ1 ++ Γ2) (csubst v #|Γ1| b).
Proof.
  intros Γ1 Γ2 x v b sub_v.
  revert Γ1 x; induction b; 
  intros Γ1 x sub_b; inversion sub_b.
  remember (Γ1 ++ x :: Γ2) as Γ.
  - simpl. constructor.
  - simpl. subst. destruct (#|Γ1| ?= n) eqn:Ec.
    + apply (subset_weaken_many [] (Γ1 ++ Γ2) v) in sub_v.
      apply sub_v.
    + eapply S_tRel. admit.
    + eapply S_tRel. admit.
  - simpl. constructor.
    apply (IHb (x0 :: Γ1) x). apply H0.
  - simpl. constructor. 
    apply (IHb1 Γ1 x); assumption.
    apply (IHb2 Γ1 x); assumption.
Admitted.

(* Lemma everything in global env is in subset*)
Lemma val_in_sub : forall Σ Γ t v,
  Σ e⊢ t ⇓ v ->
  InSubset Γ t ->
  InSubset Γ v.
Proof.
  intros Σ Γ t v ev sub. induction ev; inversion sub; subst.
  - constructor.
  - specialize (IHev1 H1). invs IHev1.
    specialize (IHev2 H2). apply IHev3.
    apply subset_closed in H0 as b_closed. admit.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. inversion H1.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - constructor. apply IHev1. apply H1. apply IHev2. apply H2.
  - constructor.
  - assumption.
  - assumption.
  - assumption.
Admitted.

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
  - (* fix case *) inversion sub_v. admit.
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
