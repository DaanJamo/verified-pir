From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import PIR BigStepPIR Translation.

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
  | S_tApp : forall x b t2,
    InSubset (x :: Γ) b ->
    InSubset Γ (tLambda (BasicAst.nNamed x) b) ->
    InSubset Γ t2 ->
    InSubset Γ (tApp (tLambda (BasicAst.nNamed x) b) t2)
.

Import Coq.Strings.String.
Local Open Scope string_scope.
Import MCMonadNotation.

Notation "pt '⇓ₚ' pv" :=
  (evaluatesTo pt pv)
  (at level 50).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac tl_reflect  Htl  := apply translate_reflect in Htl  as ?tlt.
Ltac tlt_reflect Htlt := apply translate_reflect in Htlt as ?tl.

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

Theorem refl_tl_correct : forall Σ Γ gt (ann : annots box_type gt) pt,
  Σ e⊢ gt ⇓ gt ->
  InReflSubset Γ gt ->
  (translate_term remap_env Γ gt ann) = Some pt ->
  pt ⇓ₚ pt.
Proof with (eauto using eval).
  intros Σ Γ gt ann pt ev rsub tl.
  destruct rsub.
  - (* TBox *) inversion tl. solve_pir_eval.
  - (* tRel, either a translation error or ev is invalid *) 
    now inversion ev.
  - (* tLambda *) tl_reflect tl. 
    inversion tlt. solve_pir_eval.
Qed.

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
  - inversion H1. 
    apply (fresh_axiom Γ x x0) in nIn as nIn_ext.
    tl_reflect H10. tl_reflect H1. tl_reflect H4.
    specialize (IHsub1 ann_b nIn_ext b' tlt0).
    specialize (IHsub2 ann_t1 nIn t1' tlt1).
    specialize (IHsub3 ann_t2 nIn t2' tlt2).
    simpl. (* rewrites under let-binders *) admit.
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
  - inversion tlt. inversion H1.
    tl_reflect H10. tl_reflect H1. tl_reflect H4.
    specialize (IHsub1 ann_b b' tlt0).
    specialize (IHsub2 ann_t1 t1' tlt1).
    specialize (IHsub3 ann_t2 t2' tlt2).
    simpl. destruct IHsub1, IHsub2, IHsub3. 
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

Theorem stlc_correct : forall (Σ : global_env) Γ 
  t (ann_t : annots box_type t) t'
  v (ann_v : annots box_type v),
  [] e⊢ t ⇓ v ->
  InSubset Γ t ->
  translatesTo remap_env Γ t ann_t t' ->
  exists ann_v v' k,
    translatesTo remap_env Γ v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros Σ Γ t ann_t t' v ann_v ev. revert t'.
  induction ev; intros t'' sub tlt_t; inversion sub.
  - subst. inversion ev1.
  - (* apply, the sensible case which requires subst-lemma *) admit.
  - (* mkApps case *) subst. admit.
  - (* fix case *) subst. inversion ev1. subst. admit.
  - inversion tlt_t. subst. inversion ev1.
  - (* mkApps constr case *) inversion tlt_t. subst. inversion H6. subst.
    admit.
  - subst. inversion ev1. subst. simpl in i. discriminate.
  - subst. inversion tlt_t. exists ann. exists t''.
    subst. eexists. split. apply tlt_tt. apply E_Constant. eauto.
  - subst. inversion i.
  - subst. exists ann_t. exists t''. inversion tlt_t. 
    subst. eexists. split. apply tlt_t. apply E_LamAbs. eauto.
Admitted.
  
  
