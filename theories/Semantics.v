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

Definition gal_id :=
  tLambda (BasicAst.nNamed "x"%bs) (tRel 0).

Lemma weaken_ctx : forall Σ' Γ x t ann t',
  translatesTo remap_env Σ' Γ t ann t' ->
  translatesTo remap_env Σ' (Γ ++ [x]) t ann t'.
Proof.
  intros Σ' Γ x t. revert Γ.
  induction t; intros Γ ann t' tlt;
  inversion tlt; subst.
  - constructor.
  - apply tlt_rel. now apply find_index_weaken.
  - apply inj_pair2 in H2. subst.
    apply tlt_lambda. 
    + assumption.
    + now apply (IHt (x' :: Γ)).
  - apply inj_pair2 in H3. subst.
    apply tlt_let.
    + assumption.
    + now apply IHt1.
    + now apply (IHt2 (x' :: Γ)).
  - apply inj_pair2 in H2. subst. 
    apply tlt_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - now eapply tlt_const.
Qed.

Lemma weaken_ctx_many : forall Σ' Γ1 Γ2 t ann t',
  translatesTo remap_env Σ' Γ1 t ann t' ->
  translatesTo remap_env Σ' (Γ1 ++ Γ2) t ann t'.
Proof.
  intros Σ' Γ1 Γ2 t. revert Γ1. induction t;
  intros Γ1 ann t' tlt_t; 
  inversion tlt_t; subst.
  - constructor.
  - apply tlt_rel. now apply find_index_weaken.
  - apply inj_pair2 in H2. subst.
    apply tlt_lambda. 
    + assumption.
    + now apply (IHt (x' :: Γ1)).
  - apply inj_pair2 in H3. subst.
    apply tlt_let.
    + assumption.
    + now apply IHt1.
    + now apply (IHt2 (x' :: Γ1)).
  - apply inj_pair2 in H2. subst.
    apply tlt_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - now eapply tlt_const.
Qed.

Lemma strengthen_shadowed_ctx : forall Σ' Γ x b ann_b b',
  In x Γ ->
  translatesTo remap_env Σ' (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Σ' Γ b ann_b b'.
Proof.
  intros Σ' Γ x b. revert Γ. induction b;
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
  - apply inj_pair2 in H3. subst.
    apply tlt_let.
    + assumption.
    + now apply IHb1.
    + apply (IHb2 (x' :: Γ)).
      * now right.
      * assumption.
  - apply inj_pair2 in H2. subst.
    apply tlt_app.
    + apply IHb1; assumption.
    + apply IHb2; assumption.
  - now eapply tlt_const.
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

Lemma csubst_shadowed : forall Σ' Γ x b ann_b b' v ann_v,
  In x Γ ->
  translatesTo remap_env Σ' (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Σ' (Γ ++ [x]) (csubst v (List.length Γ) b) (annot_csubst ann_v (List.length Γ) ann_b) b'.
Proof.
  intros Σ' Γ x b. revert Γ. induction b; 
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
  - apply inj_pair2 in H3. subst.
    specialize (IHb1 Γ ann_br br' v).
    specialize (IHb2 (x' :: Γ) ann_b0 b'0 v).
    simpl in *. apply tlt_let; auto.
  - apply inj_pair2 in H2. subst. 
    simpl. apply tlt_app.
    + apply IHb1; auto.
    + apply IHb2; auto.
  - now eapply tlt_const.
Qed.

Lemma csubst_correct : forall Σ' Γ x v b ann_v ann_b v' b',
  ~ In x Γ ->
  translatesTo remap_env Σ' nil v ann_v v' ->
  translatesTo remap_env Σ' (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env Σ' Γ (csubst v (List.length Γ) b)
  (annot_csubst ann_v (List.length Γ) ann_b)
  (BigStepPIR.subst x v' b').
Proof.
  intros Σ' Γ x v b. revert Γ. induction b;
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
        specialize (csubst_shadowed Σ' (x :: Γ) x b ann_b0 b'0 v ann_v Hin H4).
        intros. simpl in H.
        specialize (strengthen_shadowed_ctx Σ' (x :: Γ) x (csubst v (S #|Γ|) b) (annot_csubst ann_v (S #|Γ|) ann_b0) b'0 Hin H) as Hctx'.
        apply Hctx'.
    + apply tlt_lambda.
      * assumption.
      * apply IHb; auto. now apply not_in_cons.
  - apply inj_pair2 in H3. subst.
    simpl. destruct_str_eq x x'.
    + apply tlt_let.
      * assumption.
      * now apply IHb1. 
      * subst x'. assert (Hin : In x (x::Γ)) by now left.
        specialize (csubst_shadowed Σ' (x :: Γ) x b2 ann_b0 b'0 v ann_v Hin H6).
        intros. simpl in H.
        specialize (strengthen_shadowed_ctx Σ' (x :: Γ) x (csubst v (S #|Γ|) b2) (annot_csubst ann_v (S #|Γ|) ann_b0) b'0 Hin H) as Hctx'.
        apply Hctx'.
    + apply tlt_let.
      * assumption.
      * apply IHb1; assumption.
      * simpl. assert (~ In x (x' :: Γ)) by now apply not_in_cons.
        apply IHb2; assumption.
  - apply inj_pair2 in H2. subst.
    specialize (IHb1 Γ ann_v ann_t1 v' t1' HnIn tlt_v H1).
    specialize (IHb2 Γ ann_v ann_t2 v' t2' HnIn tlt_v H4).
    now apply tlt_app.
  - simpl. (* shadowed or in Σ' *) admit.
Admitted.

Theorem stlc_correct : forall Σ Σ'
  t (ann_t : annots box_type t) t'
  v (ann_v : annots box_type v),
  Σ e⊢ t ⇓ v ->
  InSubset [] t ->
  InSubset [] v ->
  translate_term remap_env Σ' [] t ann_t = Some t' ->
  exists ann_v v' k,
    translatesTo remap_env Σ' [] v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros Σ Σ' t ann_t t' v ann_v ev sub_t sub_v tlt.
  apply translate_reflect in tlt; try apply NoDup_nil.
  revert t' tlt; induction ev; 
  intros t'' tlt; inversion sub_t.
  - (* □ applied to values, temporary nonsensible case *) admit. 
  - (* apply *)
    inversion tlt. subst.
    evar (ann_l : annots box_type (tLambda na b)).
    evar (ann_a : annots box_type a').
    eapply val_in_sub in ev1 as sub_lambda; eauto.
    eapply val_in_sub in ev2 as sub_arg; eauto.
    destruct (IHev1 ann_t1 ann_l H1 sub_lambda t1' H5) as [ann_v1 [v1' [k1 [tlt_l ev_l]]]].
    destruct (IHev2 ann_t2 ann_a H2 sub_arg t2' H8) as [ann_v2 [v2' [k2 [tlt_v2 ev_v2]]]].
    inversion tlt_l. subst.
    assert (tlt_sb : translatesTo remap_env Σ' [] (csubst a' 0 b) (annot_csubst ann_v2 0 ann_b) (BigStepPIR.subst x' v2' b')).
    { eapply csubst_correct; auto. }
    apply tlt_in_sub in tlt_sb as sub_sb.
    specialize (IHev3 (annot_csubst ann_v2 0 ann_b) ann_v sub_sb sub_v (subst x' v2' b') tlt_sb).
    destruct IHev3 as [ann_v' [v' [k3 [tlt_v ev_v]]]].
    exists ann_v'. exists v'. eexists. split.
    + apply tlt_v.
    + eapply E_Apply. 
      * eexists.
      * apply ev_l.
      * apply ev_v2.
      * apply ev_v.
  - (* let *)
    inversion tlt. apply inj_pair2 in H8. subst.
    evar (ann_brv : annots box_type b0').
    eapply val_in_sub in ev1 as sub_br; eauto.
    destruct (IHev1 ann_br ann_brv H1 sub_br br' H10) as [ann_v1 [v1' [k1 [tlt_br ev_br]]]].
    assert (tlt_sb : translatesTo remap_env Σ' [] (csubst b0' 0 b1) (annot_csubst ann_v1 0 ann_b) (BigStepPIR.subst x'0 v1' b')).
    { eapply csubst_correct; auto. }
    apply tlt_in_sub in tlt_sb as sub_sb.
    specialize (IHev2 (annot_csubst ann_v1 0 ann_b) ann_v sub_sb sub_v (subst x'0 v1' b') tlt_sb).
    destruct IHev2 as [ann_v' [v' [k2 [tlt_v ev_v]]]].
    exists ann_v'. exists v'. eexists. split.
    + apply tlt_v.
    + eapply E_Let. eapply E_Let_TermBind_Strict.
      * eexists.
      * apply ev_br.
      * eapply E_Let_Nil.
        ** eexists.
        ** simpl. fold subst. apply ev_v.
  - (* mkApps fix *) 
    eapply val_in_sub in ev1 as sub_apps; eauto.
    apply mkApps_in_subset in sub_apps as [sub_f _]. 
    inversion sub_f.
  - (* fix guarded *) 
    inversion sub_v.
    apply mkApps_in_subset in H5 as [sub_fix _].
    inversion sub_fix.
  - (* fix unguarded *)
    eapply val_in_sub in ev1 as sub_fix; eauto.
    inversion sub_fix.
  - (* const *)
    (* evar (ann_b : annots box_type body).
    specialize (IHev ann_b ann_v). unfold EGlobalEnv.declared_constant in isdecl. *)
    admit.
  - (* mkApps constr *)
    eapply val_in_sub in ev1 as sub_apps; eauto.
    apply mkApps_in_subset in sub_apps as [sub_constr _].
    inversion sub_constr.
  - (* Atoms applied to values *)
    subst. induction f16; inversion H1.
    + inversion ev1. subst. inversion i.
    + rewrite List.nth_error_nil in H0. discriminate H0.
    + inversion ev1. subst. inversion i.
    + subst. admit.
(*  (* Atoms *)
  - subst. inversion tlt. exists ann. exists t''.
    subst. eexists. split. 
    + apply tlt_tt. 
    + apply E_Constant. eauto.
  - (* rel *) subst. inversion i.
  - (* lambda *) subst. exists ann_t. exists t''. inversion tlt. 
    subst. eexists. split. 
    + apply tlt. 
    + apply E_LamAbs. eauto. *)
Admitted.
