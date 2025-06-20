From MetaCoq.Erasure.Typed Require Import Utils WcbvEvalAux.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.

Import Coq.Strings.String.

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

Lemma csubst_in_sub' : forall (Γ1 Γ2 : list bs) x v b,
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

Lemma csubst_in_sub : forall (Γ : list bs) x v b,
  InSubset [] v ->
  InSubset (Γ ++ [x]) b ->
  InSubset (Γ) (csubst v #|Γ| b).
Proof.
  intros. assert (forall t, InSubset Γ t = InSubset (Γ ++ []) t) by (rewrite app_nil_r; reflexivity).
  rewrite H1. eapply (csubst_in_sub' Γ [] x v b); assumption.
Qed.

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
