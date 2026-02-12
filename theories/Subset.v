From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure.Typed Require Import Utils ResultMonad.
From MetaCoq.Erasure.Typed Require Import Annotations WcbvEvalAux.
From MetaCoq.Erasure Require Import EAst ECSubst EGlobalEnv ELiftSubst EWellformed.
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
    (* f <> tBox *)
    InSubset eΣ Γ f ->
    InSubset eΣ Γ a ->
    InSubset eΣ Γ (tApp f a)
  | S_tConst : forall kn decl cb,
    declared_constant (trans_env eΣ) kn decl ->
    decl.(EAst.cst_body) = Some cb ->
    InSubset eΣ [] cb ->
    InSubset eΣ Γ (tConst kn).

Inductive EnvInSubset : global_env -> Prop :=
  | ES_empty : EnvInSubset []
  | ES_const : forall (eΣ : global_env) kn deps decl cb,
      decl.(cst_body) = Some cb ->
      InSubset eΣ [] cb ->
      EnvInSubset eΣ ->
      EnvInSubset (((kn, deps), ConstantDecl decl) :: eΣ)
  | ES_remapped : forall eΣ kn deps ind,
      find (fun nm : kername => kn == nm) pir_ignore_default = Some kn ->
      EnvInSubset eΣ ->
      EnvInSubset (((kn, deps), InductiveDecl ind) :: eΣ).

Definition all_in_subset eΣ :=
  forall c decl, 
    declared_constant (trans_env eΣ) c decl -> 
    exists t, EAst.cst_body decl = Some t /\ InSubset eΣ [] t.

Inductive ProgramInSubset (eΣ : global_env) (init : kername) : Prop :=
  | PS_Constants :
    EnvInSubset eΣ ->
    (exists t, declared_constant (trans_env eΣ) init t) ->
    ProgramInSubset eΣ init.

Fixpoint annots_sensible (TT : Env.env ty) t (ann_t : annots box_type t) : bool :=
  match t, ann_t with
  | tBox, TBox => true
  | tLambda x b, (TArr dom _, ann_b) => isSome (translate_ty TT dom) && annots_sensible TT b ann_b
  | tLambda x b, _ => false
  | tLetIn x v b, (TArr dom _, (ann_v, ann_b)) => isSome (translate_ty TT dom) && 
      annots_sensible TT v ann_v && annots_sensible TT b ann_b
  | tLetIn x v b, _ => false
  | tApp f a, (ty, (ann_f, ann_a)) => annots_sensible TT f ann_f && annots_sensible TT a ann_a
  | _, _ => true (* the definition of correctness for the other constructors should be refined further *) 
  end.

Definition constant_annots_sensible
           (TT : Env.env ty) (ignore : list kername) 
           (cb : constant_body) (ann_cb : constant_body_annots box_type cb) : bool.
Proof.
  destruct cb, cst_body.
  - hnf in ann_cb. exact (annots_sensible TT t ann_cb).
  - exact false.
Qed.

Fixpoint env_annots_sensible 
         (TT : Env.env ty) (ignore : list kername) 
         (eΣ : global_env) (ann_env : env_annots box_type eΣ) : bool :=
  match eΣ, ann_env with
  | [], tt => true
  | (((_, _), ConstantDecl cb)::eΣ'), (ann_decl, ann_env') => 
      constant_annots_sensible TT ignore cb ann_decl && env_annots_sensible TT ignore eΣ' ann_env'
  | (((kn, _), InductiveDecl _)::eΣ'), (ann_decl, ann_env') => 
      isSome (find (fun nm : kername => kn == nm) ignore) && env_annots_sensible TT ignore eΣ' ann_env'
  | _, _ => false
  end.

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

(* Γ needs to be both [] for substitution and the same as t for tRel *)
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
    + admit. 
    + apply H0.
  - specialize (IHev1 Γ H1).
    apply IHev2.
    eapply (csubst_in_sub' eΣ [] Γ).
    + admit.
    + apply H3.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. apply mkApps_in_subset in H1 as [Hf _]. inversion Hf.
  - apply IHev1 in H1. inversion H1.
  - assert (decl = decl0 /\ body = cb) by eauto using declared_constant_same.
    destruct H. subst. apply IHev.
    now eapply (subset_weaken_many eΣ []).
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
  - eapply S_tConst; 
    (* needs link between constant and entry *) admit.
Admitted.

(* needs a link between names and their fresh names *)
Lemma subset_is_translatable : forall TT eΣ Σ' Γ t ann_t,
  InSubset eΣ Γ t ->
  annots_sensible TT t ann_t = true ->
  exists t', translate_term TT Σ' Γ t ann_t = Some t'.
Proof.
  intros TT eΣ Σ' Γ t ann_t sub Hty.
  induction sub; subst.
  - eexists. constructor.
  - exists (Var res).
    simpl. now rewrite H.
  - destruct ann_t as [[] ann_b]; try discriminate.
    simpl in Hty. apply andb_true_iff in Hty as [tl_ty Hty].
    destruct (IHsub ann_b Hty) as [b' tl_b].
    destruct (translate_ty TT dom) as [ty'|] eqn:tl_ty'; try discriminate.
    assert (x' = gen_fresh_name x Σ' Γ). admit.
    simpl. subst.
    exists (LamAbs (gen_fresh_name x Σ' Γ) ty' b').
    now rewrite tl_ty', tl_b.
  - destruct ann_t as [[] [ann_br ann_b]]; try discriminate.
    simpl in Hty. apply andb_true_iff in Hty as [Hty Hty_b].
    apply andb_true_iff in Hty as [Hty Hty_br].
    destruct (translate_ty TT dom) as [ty'|] eqn:tl_ty'; try discriminate.
    destruct (IHsub1 ann_br Hty_br) as [br' tl_br].
    destruct (IHsub2 ann_b Hty_b) as [b' tl_b].
    eexists (Let [TermBind (VarDecl (gen_fresh_name x Σ' Γ) ty') br'] b').
    simpl. assert (x' = gen_fresh_name x Σ' Γ). admit. rewrite <- H.
    now rewrite tl_ty', tl_br, tl_b.
  - destruct ann_t as [ty [ann_f ann_a]].
    simpl in Hty. apply andb_true_iff in Hty as [Hty_f Hty_a].
    destruct (IHsub1 ann_f Hty_f) as [f' tl_f].
    destruct (IHsub2 ann_a Hty_a) as [a' tl_a].
    eexists. simpl. now rewrite tl_f, tl_a.
Admitted.

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

Lemma wellformed_implies_subset : forall eΣ Γ t,
  @wellformed subset_env_flags (trans_env eΣ) (List.length Γ) t = true ->
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
  - unfold EGlobalEnv.lookup_constant in H0.
    destruct (EGlobalEnv.lookup_env (trans_env eΣ) k) as [[]|] eqn:Hl; try discriminate.
    destruct c as [[]]; try discriminate.
    eapply (S_tConst eΣ Γ k {| Extract.E.cst_body := Some t |} t).
    + eauto.
    + eauto.
    + (* constant_bodies in the environment should be in the subset too *) admit.
  - destruct prim as [[]]; inversion Hwf.
Admitted.

Lemma wf_glob_implies_env_subset : forall eΣ,
  @wf_glob subset_env_flags (trans_env eΣ) ->
  (forall kn ind, wf_minductive ind ->
    find (fun nm : kername => kn == nm) pir_ignore_default = Some kn) ->
  EnvInSubset eΣ.
Proof.
  intros eΣ Hwf Hind.
  induction eΣ.
  - econstructor.
  - inversion Hwf. subst.
    destruct a as [[a_kn deps] a_cb].
    destruct a_cb; try discriminate.
    + destruct c.
      destruct cst_body; try discriminate.
      simpl in *. hnf in H3. 
      eapply (wellformed_implies_subset eΣ []) in H3.
      econstructor; simpl; try eauto.
    + simpl in H3. eapply Hind in H3.
      now econstructor.
    + destruct o; simpl in *.
      (* type aliases not supported *)
      * admit.
      * admit.
Admitted.
