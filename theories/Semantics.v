From MetaCoq.Erasure.Typed Require Import ExAst Utils WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
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
  | S_tLambda : forall x b,
    InSubset (x :: ctx) b ->
    InSubset ctx (tLambda (BasicAst.nNamed x) b)
  | S_tApp : forall t1 t2,
    InSubset ctx t1 ->
    InSubset ctx t2 ->
    InSubset ctx (tApp t1 t2)
.

Lemma sub_ctx_ext : forall ctx x t,
  InSubset ctx t ->
  InSubset (x :: ctx) t.
Proof.
  intros ctx x t sub.
  induction sub.
  - constructor.
  - simpl. admit.
  - constructor. admit.
  - simpl. constructor. apply IHsub1. apply IHsub2.
Admitted.

Import Coq.Strings.String.
Local Open Scope string_scope.
Import MCMonadNotation.

Notation "pt '⇓ₚ' pv" :=
  (evaluatesTo pt pv)
  (at level 50).

Ltac solve_pir_eval := split; [(eexists ; eauto using eval) | constructor].
Ltac tl_reflect H := apply translate_reflect in H.

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
  tl_reflect tl.
  inversion tl. solve_pir_eval.
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
  tl_reflect tl_a.
  inversion tl_a.
  exists ann_t1. exists ann_t2. exists t1'. exists t2'.
  tl_reflect H1. tl_reflect H4. auto.
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
  - (* tLambda *) tl_reflect tl. 
    inversion tl. solve_pir_eval.
Qed.

Definition id_app := tApp
  (tLambda (BasicAst.nNamed "x"%bs) (tRel 0)) (tBox).

Print ELiftSubst.subst.
Print csubst.
Print annots.
Print tLambda.

Print gal_id.
Eval cbv in csubst 
  (tLambda (BasicAst.nNamed "y"%bs) (tRel 0))
  0
  gal_id.
Eval cbv in (tLambda (BasicAst.nNamed "x"%bs (tLambda (BasicAst.nNamed "y"))))

Print eval.
Lemma tl_subst : forall ctx k x v b ann_v ann_b ann_t v' b',
  (* closed  *)
  (* nth_error ctx k = Some x -> *)
  translatesTo remap_env ctx v ann_v v' ->
  translatesTo remap_env ctx b ann_b b' ->
  translatesTo remap_env ctx (csubst v k b) ann_t (BigStepPIR.subst x v' b').
Proof.
  intros ctx k x v b ann_v ann_b ann_t v' b'. revert ctx k ann_t b'.
  induction b; intros ctx k' ann_t b' tlt_v tlt_b; inversion tlt_b.
  - apply tlt_tt.
  (* - destruct (k' =? n)%nat eqn:Enk.
    rewrite Nat.eqb_eq in Enk. *)
  - simpl in *. destruct (x =? (bs_to_s x0)).
    + destruct (k' ?= n)%nat eqn:ekn.
      * admit. (* ann_t must be ann_v, how to prove this *)
      * admit.
      * admit.
    + destruct (k' ?= n)%nat eqn:ekn.
      * admit.
      * admit.
      * subst. admit.
  - destruct ann_t as [ty ann_sb].
    simpl in *. destruct (x =? (bs_to_s x0)).
    + admit.
    + admit.
  - simpl in *.
    destruct ann_t as [t_ty [ann_st1 ann_st2]].
    specialize (IHb1 ann_t1 ctx k' ann_st1 t1' tlt_v H1).
    specialize (IHb2 ann_t2 ctx k' ann_st2 t2' tlt_v H4).
    apply (tlt_app remap_env ctx). apply IHb1. apply IHb2.
Admitted.

(* lemma for general and closed *)
Theorem stlc_correct : forall Σ ctx 
  t (ann_t : annots box_type t) t'
  v (ann_v : annots box_type v),
  [] e⊢ t ⇓ v ->
  InSubset nil t ->
  translatesTo remap_env ctx t ann_t t' ->
  exists ann_v v' k,
    translatesTo remap_env ctx v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros Σ ctx t ann_t t' v ann_v ev. revert t'.
  induction ev; intros t'' sub tlt_t; inversion sub.
  - admit.
  - inv tlt_t.
    admit.
  - admit.
  - admit.
  - Admitted.
  
  
