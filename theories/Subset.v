From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure.Typed Require Import Utils ResultMonad.
From MetaCoq.Erasure.Typed Require Import Annotations WcbvEvalAux.
From MetaCoq.Erasure Require Import EAst ECSubst EGlobalEnv ELiftSubst.
From MetaCoq.Erasure.Typed Require Import ExAst.

From VTL Require Import PIR BigStepPIR Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.

From Coq Require Import Strings.String Lia.

Inductive InSubset (eΣ : global_env) (Γ : list string) : EAst.term -> Prop :=
  | S_tBox : InSubset eΣ Γ tBox
  | S_tRel : forall n res,
    nth_error Γ n = Some res ->
    InSubset eΣ Γ (tRel n)
  | S_tLambda : forall x x' b,
    InSubset eΣ (x' :: Γ) b ->
    InSubset eΣ Γ (tLambda x b)
  | S_tLet : forall x x' br b,
    InSubset eΣ Γ br ->
    InSubset eΣ (x' :: Γ) b ->
    InSubset eΣ Γ (tLetIn x br b)
  | S_tApp : forall f a,
    InSubset eΣ Γ f ->
    InSubset eΣ Γ a ->
    InSubset eΣ Γ (tApp f a)
  | S_tConst : forall kn decl cb,
    declared_constant (trans_env eΣ) kn decl ->
    decl.(EAst.cst_body) = Some cb ->
    InSubset eΣ [] cb ->
    InSubset eΣ Γ (tConst kn)
.

(* Definition declared_constant (eΣ : global_env) kn c : Prop :=
  lookup_env eΣ kn = Some (ConstantDecl c). *)

Definition all_in_subset eΣ :=
  forall c decl, 
    declared_constant (trans_env eΣ) c decl -> 
    exists t, EAst.cst_body decl = Some t /\ InSubset eΣ [] t.

Inductive ProgramInSubset (eΣ : global_env) (init : kername) : Prop :=
  | PS_Constants :
    all_in_subset eΣ ->
    (exists t, declared_constant (trans_env eΣ) init t) ->
    ProgramInSubset eΣ init.

Lemma mkApps_in_subset : forall eΣ Γ us f,
  InSubset eΣ Γ (mkApps f us) ->
  InSubset eΣ Γ f /\ (forall a, In a us -> InSubset eΣ Γ a).
Proof.
  intros eΣ Γ us. induction us.
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

Lemma subset_weaken : forall eΣ Γ x t,
  InSubset eΣ Γ t ->
  InSubset eΣ (Γ ++ [x]) t.
Proof.
  intros eΣ Γ x t sub. induction sub.
  - constructor.
  - apply (S_tRel eΣ (Γ ++ [x]) n res). 
    apply nth_error_Some_length in H as Hl.
    rewrite (nth_error_app1 Γ [x] Hl). assumption.
  - eapply S_tLambda. apply IHsub.
  - eapply S_tLet. apply IHsub1. apply IHsub2.
  - apply S_tApp; assumption.
  - eapply S_tConst; eassumption.
Qed.

Lemma subset_weaken_many : forall eΣ Γ1 Γ2 t,
  InSubset eΣ Γ1 t ->
  InSubset eΣ (Γ1 ++ Γ2) t.
Proof.
  intros eΣ Γ1 Γ2 t sub. induction sub.
  - constructor.
  - apply (S_tRel eΣ (Γ ++ Γ2) n res). 
    apply nth_error_Some_length in H as Hl.
    rewrite (nth_error_app1 Γ Γ2 Hl). assumption.
  - eapply S_tLambda. apply IHsub.
  - eapply S_tLet. apply IHsub1. apply IHsub2.
  - apply S_tApp; assumption.
  - eapply S_tConst; eassumption.
Qed.

Lemma csubst_in_sub' : forall eΣ Γ1 Γ2 x v b,
  InSubset eΣ [] v ->
  InSubset eΣ (Γ1 ++ x :: Γ2) b ->
  InSubset eΣ (Γ1 ++ Γ2) (csubst v #|Γ1| b).
Proof.
  intros eΣ Γ1 Γ2 x v b sub_v.
  revert Γ1 x; induction b; 
  intros Γ1 x sub_b; inversion sub_b.
  remember (Γ1 ++ x :: Γ2) as Γ.
  - simpl. constructor.
  - simpl. subst. destruct (#|Γ1| ?= n) eqn:Ec.
    + apply (subset_weaken_many eΣ [] (Γ1 ++ Γ2) v) in sub_v.
      apply sub_v.
    + apply Nat.compare_lt_iff in Ec.
      apply nth_error_Some_length, length_pred_middle in H0.
      apply nth_error_Some_value in H0. destruct H0.
      apply (S_tRel eΣ (Γ1 ++ Γ2) (Nat.pred n) x0 H). assumption.
    + apply Nat.compare_gt_iff in Ec.
      apply length_extend with (l2 := Γ2) in Ec.
      apply nth_error_Some_value in Ec. destruct Ec.
      apply (S_tRel eΣ (Γ1 ++ Γ2) n x0 H).
  - simpl. econstructor.
    apply (IHb (x' :: Γ1) x). apply H0.
  - simpl. econstructor.
    apply (IHb1 Γ1 x); assumption.
    apply (IHb2 (x' :: Γ1) x); assumption.
  - simpl. constructor. 
    apply (IHb1 Γ1 x); assumption.
    apply (IHb2 Γ1 x); assumption.
  - eapply S_tConst; eassumption.
Qed.

Lemma csubst_in_sub : forall eΣ (Γ : list string) x v b,
  InSubset eΣ [] v ->
  InSubset eΣ (Γ ++ [x]) b ->
  InSubset eΣ Γ (csubst v #|Γ| b).
Proof.
  intros. assert (forall t, InSubset eΣ Γ t = InSubset eΣ (Γ ++ []) t) by (rewrite app_nil_r; reflexivity).
  rewrite H1. eapply (csubst_in_sub' eΣ Γ [] x v b); assumption.
Qed.

Lemma val_in_sub : forall eΣ Γ t v,
  (trans_env eΣ) e⊢ t ⇓ v ->
  InSubset eΣ Γ t ->
  InSubset eΣ Γ v.
Proof.
  intros eΣ Γ t v ev. revert Γ. induction ev; intros Γ sub; inversion sub; subst.
  - constructor.
  - specialize (IHev1 Γ H1). invs IHev1.
    specialize (IHev2 Γ H2). apply IHev3.
    eapply (csubst_in_sub' eΣ [] Γ).
    admit. apply H0.
  - specialize (IHev1 Γ H1).
    apply IHev2.
    eapply (csubst_in_sub' eΣ [] Γ).
    admit. apply H3.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. inversion H1.
  - (* const *) admit.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - constructor. apply IHev1. apply H1. apply IHev2. apply H2.
  - constructor.
  - assumption.
  - assumption.
  - assumption.
Admitted.

Lemma tlt_in_sub : forall TT eΣ Σ' Γ t ann t',
  translatesTo TT Σ' Γ t ann t' ->
  InSubset eΣ Γ t.
Proof.
  intros. induction H; subst.
  - constructor.
  - econstructor. now apply find_index_to_nth_error in H.
  - now eapply S_tLambda.
  - now eapply S_tLet.
  - now apply S_tApp.
  - eapply S_tConst.
Admitted.

(* notion of typablility under the remapping *)
Lemma subset_is_translatable : forall TT eΣ Σ' Γ t,
  InSubset eΣ Γ t ->
  exists ann t', translate_term TT Σ' Γ t ann = Some t'.
Proof.
  intros TT eΣ Σ' Γ t sub. 
  induction sub; subst.
  - eexists _, _. constructor.
  - eexists. exists (Var res).
    simpl. now rewrite H.
  - destruct IHsub as [ann_b [b' tl_b]].
    evar (f_ty : ExAst.box_type).
    evar (f_ty' : PIR.ty).
    simpl. eexists ((ExAst.TArr f_ty _), ann_b), (LamAbs (gen_fresh_name x Σ' Γ) f_ty' b').
    assert (translate_ty TT f_ty = Some f_ty'). admit.
    assert (x' = gen_fresh_name x Σ' Γ). admit. rewrite <- H0.
    rewrite H, tl_b. simpl. reflexivity.
  - destruct IHsub1 as [ann_br [br' tl_br]].
    destruct IHsub2 as [ann_b [b' tl_b]].
    evar (br_ty : ExAst.box_type).
    evar (br_ty' : PIR.ty).
    simpl. eexists (ExAst.TArr br_ty _, (ann_br, ann_b)), (Let [TermBind (VarDecl (gen_fresh_name x Σ' Γ) br_ty') br'] b').
    assert (translate_ty TT br_ty = Some br_ty'). admit.
    assert (x' = gen_fresh_name x Σ' Γ). admit. rewrite <- H0.
    rewrite H, tl_br, tl_b. simpl. reflexivity.
  - destruct IHsub1 as [ann_t1 [t1' tl_t1]].
    destruct IHsub2 as [ann_t2 [t2' tl_t2]].
    simpl. eexists (_, (ann_t1, ann_t2)), (Apply t1' t2').
    now rewrite tl_t1, tl_t2.
Admitted.

Import EWellformed.

Definition subset_primitive_flags :=
{|
  has_primint := false;
  has_primfloat := false;
  has_primstring := false;
  has_primarray := false
|}.

Definition subset_term_flags :=
  {| has_tBox := true;
     has_tRel := true;
     has_tVar := false;
     has_tEvar := false;
     has_tLambda := true;
     has_tLetIn := true;
     has_tApp := true;
     has_tConst := true;
     has_tConstruct := false;
     has_tCase := false;
     has_tProj := false;
     has_tFix := false;
     has_tCoFix := false;
     has_tPrim := subset_primitive_flags;
     has_tLazy_Force := false
  |}.

Definition subset_env_flags :=
  {| has_axioms := false;
     term_switches := subset_term_flags;
     has_cstr_params := false;
     cstr_as_blocks := false
  |}.

Local Existing Instance subset_env_flags.

Lemma lookup_env_context : forall eΣ kn c,
  EGlobalEnv.lookup_env (trans_env eΣ) kn = Some (EAst.ConstantDecl c) ->
  exists c', lookup_constant eΣ kn = Some c'.
Proof.
  (* intros eΣ kn cb cb' t [Hl Hsome].
  induction eΣ.
  - inversion Hl.
  - destruct a as [[kn' deps] decl].
    destruct (kn == kn') eqn:Heq.
    + apply ReflectEq.eqb_eq in Heq. subst.
      unfold EGlobalEnv.lookup_constant, EGlobalEnv.lookup_env in Hl. simpl in Hl.
      unfold lookup_constant_body, lookup_constant, lookup_env. *)
      (* simpl. rewrite ReflectEq.eqb_refl. rewrite ReflectEq.eqb_refl in Hl.
      simpl in Hl. simpl. destruct cb. destruct cst_body; try discriminate.
      destruct decl; try discriminate.
      * simpl. inversion Hl. inversion Hsome. subst. destruct c. inversion Hl. admit.
      * inversion Hl. destruct o; try discriminate. inversion H0. subst. simpl in Hl.
        destruct t; try discriminate. *)
Admitted.

(* lookup_env_find *)
Lemma wf_glob_implies_subset : forall eΣ init cb,
  @wf_glob subset_env_flags (trans_env eΣ) ->
  EGlobalEnv.declared_constant (trans_env eΣ) init cb ->
  ProgramInSubset eΣ init.
Proof.
  intros eΣ init cb Hwf Hinit.
  induction eΣ.
  - inversion Hinit.
  - destruct a as [[kn deps] decl].
    inversion Hinit.
    destruct (init == kn) eqn:Heq.
    + apply ReflectEq.eqb_eq in Heq. subst.
      inversion Hinit. rewrite ReflectEq.eqb_refl in H1.
      inversion H1. cbn. inversion Hwf. subst.
      constructor. hnf. intros. inversion H. inversion H6.
      subst. eexists.
Admitted.

Lemma wellformed_implies_subset : forall eΣ Γ t,
  @wellformed subset_env_flags (trans_env eΣ) (List.length Γ) t ->
  InSubset eΣ Γ t.
Proof.
  intros eΣ Γ t. revert Γ.
  induction t; intros Γ Hwf; inversion Hwf.
  - constructor.
  - apply Nat.ltb_lt, nth_error_Some_value in H0.
    destruct H0. now eapply S_tRel.
  - pose (na' := gen_fresh_name na [] Γ).
    apply (S_tLambda eΣ Γ na na'). apply IHt. 
    simpl. apply H0.
  - apply andb_true_iff in H0 as [Hwf_t1 Hwf_t2].
    pose (na' := gen_fresh_name na [] Γ).
    apply (S_tLet eΣ Γ na na'). 
    apply IHt1; assumption.
    apply IHt2; assumption.
  - apply andb_true_iff in H0 as [Hwf_t1 Hwf_t2].
    apply (S_tApp eΣ Γ).
    apply IHt1; assumption.
    apply IHt2; assumption.
  - destruct (EGlobalEnv.lookup_constant (trans_env eΣ) k) eqn:Hl; [|discriminate].
    destruct eΣ; try discriminate. destruct p as [[k' deps] decl].
    destruct (k == k') eqn:Heq.
    + apply ReflectEq.eqb_eq in Heq. subst.
      admit.
    + econstructor. unfold EGlobalEnv.declared_constant. simpl. rewrite Heq.
      admit. admit. admit.
  - destruct prim as [[]]; inversion Hwf.
Admitted.
