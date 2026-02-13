From MetaCoq.Erasure.Typed Require Import ExAst Utils ResultMonad WcbvEvalAux.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst EWellformed.
From MetaCoq.Utils Require Import utils.

From VTL Require Import Entry PIR BigStepPIR Subset Translation Utils.

Existing Instance EWcbvEval.default_wcbv_flags.
Set Default Goal Selector "!".

Import Coq.Strings.String.
Import Coq.Logic.Eqdep.
Import MCMonadNotation.

Definition gal_id :=
  tLambda (BasicAst.nNamed "x"%bs) (tRel 0).

Lemma lookup_init : forall eΣ Σ' ann_env kn kn' decl cb,
  EGlobalEnv.declared_constant (trans_env eΣ) kn decl ->
  decl.(EAst.cst_body) = Some cb ->
  lookup_fresh (to_fresh_map Σ') kn = Some (kn, kn') ->
  translatesEnv remap_env eΣ Σ' ann_env ->
  exists Σ'' ann_cb cb', translatesTo remap_env Σ'' [] cb ann_cb cb'.
Proof.
  intros. induction H2.
  - discriminate.
  - destruct entry as [e_kn [[e_kn' ty'] e_b']].
    hnf in H. simpl in H, H1.
    destruct (kn == kn0) eqn:Heq.
    + destruct decl0.
      * destruct c. destruct cst_body; simpl in H2; try eauto.
        destruct decl; try discriminate.
        destruct cst_body; try discriminate. 
        inversion H. invs H0.
        exists (to_fresh_map Σ'). exists ann_decl. exists e_b'.
        assumption. 
      * inversion H.
      * admit.
    + eapply IHtranslatesEnv; try eauto.
      simpl in H1. destruct (e_kn == kn); try eauto.
      invs H1. admit.
Admitted.

Fixpoint subst_entries (Σ' : list entry) t {struct Σ'} :=
  match Σ' with
  | [] => t
  | ((_, TermBind (VarDecl kn' ty) b)::Σ'') => 
      BigStepPIR.subst kn' b (subst_entries Σ'' t)
  end.

Fixpoint subst_bnr_entries (Σ' : list entry) bnd {struct Σ'} :=
  match Σ' with
  | [] => bnd
  | ((_, TermBind (VarDecl kn' ty) b)::Σ'') => 
      @subst_bnr' subst_b kn' b (subst_bnr_entries Σ'' bnd)
  end.

Lemma unfold_app_subst x v' f' a' :
  BigStepPIR.subst x v' (Apply f' a') = Apply (BigStepPIR.subst x v' f') (BigStepPIR.subst x v' a').
Proof.
  eauto.
Qed.

Lemma unfold_app_subst_entries (Σ' : list entry) f' a' :
  subst_entries Σ' (Apply f' a') = Apply (subst_entries Σ' f') (subst_entries Σ' a').
Proof.
  induction Σ'.
  - eauto.
  - destruct a as [fr [[] b]].
    simpl. now rewrite <- unfold_app_subst.
Qed.

Lemma unfold_let_subst x v' bs t' :
  BigStepPIR.subst x v' (Let bs t') =
  Let (@subst_bnr' subst_b x v' bs)
      (if existsb (eqb x) (bvbs bs)
        then t'
        else BigStepPIR.subst x v' t').
Proof.
  eauto.
Qed.

Lemma unfold_let_subst_entries Σ' e_kn e_kn' e_ty e_b' bs t' :
  subst_entries ((e_kn, TermBind (VarDecl e_kn' e_ty) e_b') :: Σ')
    (Let bs t')
  =
  Let
    (@subst_bnr' subst_b e_kn' e_b' (subst_bnr_entries Σ' bs))
    (if existsb (eqb e_kn') (bvbs bs)
     then t'
     else (BigStepPIR.subst e_kn' e_b' (subst_entries Σ' t'))).
Proof.
  induction Σ'.
  - eauto.
  - destruct a as [a_kn [[nm ty] t]]. simpl in *.
    admit.
Admitted. 

Lemma subst_not_free : forall x v b,
  ~ In x (fv b) ->
  subst x v b = b.
Proof.
Admitted.

Lemma subst_comm : forall x y n l m,
  x <> y ->
  ~ In x (fv l) ->
  BigStepPIR.subst x n (BigStepPIR.subst y l m) = 
  BigStepPIR.subst y l (BigStepPIR.subst x n m).
Proof.
  intros. induction m; try eauto.
  - admit.
  - admit.
  - destruct_str_eq y b.
    + simpl. rewrite Heqb.
      destruct_str_eq x b.
      * subst. contradiction.
      * simpl. now rewrite Heqb, Heqb0.
    + simpl. rewrite Heqb.
      destruct_str_eq x b.
      * simpl. now rewrite Heqb, Heqb0.
      * simpl. now rewrite Heqb, Heqb0, IHm.
  - simpl. f_equal; eauto.
Admitted.

Lemma subst_entries_comm : forall (Σ' : list entry) x v b,
  ~ In x (map get_entry_nm Σ') ->
  BigStepPIR.subst x v (subst_entries Σ' b) = subst_entries Σ' (BigStepPIR.subst x v b).
Proof.
  intros. induction Σ'.
  - eauto.
  - destruct a as [[e_kn e_kn'] [[nm ty] t]].
    simpl in *. rewrite subst_comm.
    + f_equal. now apply IHΣ'.
    + now apply not_in_cons in H as [Hneq HnIn].
    + apply not_in_cons in H. admit.
Admitted.

Lemma eval_constant_unfolding : forall Σ' kn' b' v' k,
  ~ In kn' (map get_entry_nm Σ') ->
  eval (subst_entries Σ' b') v' k ->
  eval (subst kn' b' (subst_entries Σ' (Var kn'))) v' k.
Proof.
  intros. revert b' H0. induction Σ'; intros.
  - simpl. intros. now rewrite eqb_refl.
  - destruct a as [e_kn [[nm ty] t]].
    rewrite subst_entries_comm; try eauto.
    simpl. now rewrite eqb_refl.
Qed.

Lemma weaken_ctx : forall frmap Γ x t ann t',
  translatesTo remap_env frmap Γ t ann t' ->
  translatesTo remap_env frmap (Γ ++ [x]) t ann t'.
Proof.
  intros frmap Γ x t. revert Γ.
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

Lemma weaken_ctx_many : forall frmap Γ1 Γ2 t ann t',
  translatesTo remap_env frmap Γ1 t ann t' ->
  translatesTo remap_env frmap (Γ1 ++ Γ2) t ann t'.
Proof.
  intros frmap Γ1 Γ2 t. revert Γ1. induction t;
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

Lemma strengthen_shadowed_ctx : forall frmap Γ x b ann_b b',
  In x Γ ->
  translatesTo remap_env frmap (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env frmap Γ b ann_b b'.
Proof.
  intros frmap Γ x b. revert Γ. induction b;
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
  - destruct (k ?= n).
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

Lemma csubst_shadowed : forall frmap Γ x b ann_b b' v ann_v,
  In x Γ ->
  translatesTo remap_env frmap (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env frmap (Γ ++ [x]) 
    (csubst v (List.length Γ) b) (annot_csubst ann_v (List.length Γ) ann_b) b'.
Proof.
  intros frmap Γ x b. revert Γ. induction b; 
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

Lemma csubst_correct : forall frmap Γ x v b ann_v ann_b v' b',
  ~ In x Γ ->
  ~ In x (get_binder_names frmap) ->
  translatesTo remap_env frmap [] v ann_v v' ->
  translatesTo remap_env frmap (Γ ++ [x]) b ann_b b' ->
  translatesTo remap_env frmap Γ (csubst v (List.length Γ) b)
  (annot_csubst ann_v (List.length Γ) ann_b)
  (BigStepPIR.subst x v' b').
Proof.
  intros frmap Γ x v b. revert Γ. induction b;
  intros Γ ann_v ann_b v' b' HnIn HnIn' tlt_v tlt_b;
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
        specialize (csubst_shadowed frmap (x :: Γ) x b ann_b0 b'0 v ann_v Hin H4).
        intros. simpl in H.
        specialize (strengthen_shadowed_ctx frmap (x :: Γ) x 
          (csubst v (S #|Γ|) b) (annot_csubst ann_v (S #|Γ|) ann_b0) b'0 Hin H) as Hctx'.
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
        specialize (csubst_shadowed frmap (x :: Γ) x b2 ann_b0 b'0 v ann_v Hin H6).
        intros. simpl in H.
        specialize (strengthen_shadowed_ctx frmap (x :: Γ) x 
          (csubst v (S #|Γ|) b2) (annot_csubst ann_v (S #|Γ|) ann_b0) b'0 Hin H) as Hctx'.
        apply Hctx'.
    + apply tlt_let.
      * assumption.
      * apply IHb1; assumption.
      * simpl. assert (~ In x (x' :: Γ)) by now apply not_in_cons.
        apply IHb2; assumption.
  - apply inj_pair2 in H2. subst.
    specialize (IHb1 Γ ann_v ann_t1 v' t1' HnIn HnIn' tlt_v H1).
    specialize (IHb2 Γ ann_v ann_t2 v' t2' HnIn HnIn' tlt_v H4).
    now apply tlt_app.
  - simpl.
    destruct_str_eq x kn'.
    + apply lookup_fresh_Some in H1 as HIn'. subst. contradiction.
    + econstructor. eauto.
Qed.

Theorem stlc_correct : forall t (ann_t : annots box_type t) t' v,
  (trans_env []) e⊢ t ⇓ v ->
  InSubset [] [] t ->
  translate_term remap_env [] [] t ann_t = Some t' ->
  exists ann_v v' k,
    translatesTo remap_env [] [] v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros t ann_t t' v ev sub_t tlt.
  apply translate_reflect in tlt; try apply NoDup_nil.
  apply (val_in_sub [] [] t v ev) in sub_t as sub_v.
  revert t' tlt; induction ev; 
  intros t'' tlt; inversion sub_t.
  - (* □ applied to values, temporary nonsensible case *) admit. 
  - (* apply *)
    inversion tlt. subst.
    eapply val_in_sub in ev1 as sub_lambda; eauto.
    eapply val_in_sub in ev2 as sub_arg; eauto.
    destruct (IHev1 ann_t1 H1 sub_lambda t1' H5) as [ann_v1 [v1' [k1 [tlt_l ev_l]]]].
    destruct (IHev2 ann_t2 H2 sub_arg t2' H8) as [ann_v2 [v2' [k2 [tlt_v2 ev_v2]]]].
    inversion tlt_l. subst.
    assert (tlt_sb : translatesTo remap_env [] [] (csubst a' 0 b) (annot_csubst ann_v2 0 ann_b) (BigStepPIR.subst x' v2' b')).
    { eapply csubst_correct; auto. }
    eapply (tlt_in_sub remap_env [] [] tt) in tlt_sb as sub_sb; try constructor.
    specialize (IHev3 (annot_csubst ann_v2 0 ann_b) sub_sb sub_v (subst x' v2' b') tlt_sb).
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
    eapply val_in_sub in ev1 as sub_br; eauto.
    destruct (IHev1 ann_br H1 sub_br br' H10) as [ann_v1 [v1' [k1 [tlt_br ev_br]]]].
    assert (tlt_sb : translatesTo remap_env [] [] (csubst b0' 0 b1) (annot_csubst ann_v1 0 ann_b) (BigStepPIR.subst x'0 v1' b')).
    { eapply csubst_correct; auto. }
    eapply (tlt_in_sub remap_env [] [] tt) in tlt_sb as sub_sb; try constructor.
    specialize (IHev2 (annot_csubst ann_v1 0 ann_b) sub_sb sub_v (subst x'0 v1' b') tlt_sb).
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
  - discriminate.
  - (* mkApps constr *)
    eapply val_in_sub in ev1 as sub_apps; eauto.
    apply mkApps_in_subset in sub_apps as [sub_constr _].
    inversion sub_constr.
  - (* atoms applied to values *)
    subst. induction f16; inversion H1.
    + inversion ev1. subst. inversion i.
    + rewrite List.nth_error_nil in H0. discriminate H0.
    + inversion ev1. subst. inversion i.
    + (* apply LetIn to value *) admit.
    + (* apply Apply to value *) admit.
    + discriminate.
 (* Atoms *)
  - subst. inversion tlt. exists ann. exists t''.
    subst. eexists. split.
    + apply tlt_tt. 
    + apply E_Constant. eauto.
  - (* rel *) subst. inversion i.
  - (* lambda *) subst. exists ann_t. exists t''. inversion tlt. 
    subst. eexists. split. 
    + apply tlt.
    + apply E_LamAbs. eauto.
Admitted.

(* globals and let binding the environment *)

Theorem stlc_globals_correct : forall (eΣ : global_env) ann_env Σ'
  t (ann_t : annots box_type t) t' v,
  (trans_env eΣ) e⊢ t ⇓ v ->
  EnvInSubset eΣ ->
  translate_env remap_env eΣ ann_env = Ok Σ' ->
  InSubset eΣ [] t ->
  translate_term remap_env (to_fresh_map Σ') [] t ann_t = Some t' ->
  exists ann_v v' k,
    translatesTo remap_env (to_fresh_map Σ') [] v ann_v v' /\
    eval (subst_entries Σ' t') v' k.
Proof with (eauto using eval).
  intros eΣ ann_env Σ' t ann_t t' v.
  intros ev sub_env tle sub_t tlt.
  apply translate_env_reflect in tle.
  apply translate_reflect in tlt; try apply NoDup_nil.
  apply (val_in_sub eΣ [] t v ev) in sub_t as sub_v.
  revert Σ' t' tle tlt; induction ev; 
  intros Σ' t'' tle tlt; inversion sub_t.
  - (* □ applied to values, temporary nonsensible case *) admit. 
  - (* apply *)
    inversion tlt. subst.
    eapply val_in_sub in ev1 as sub_lambda; eauto.
    eapply val_in_sub in ev2 as sub_arg; eauto.
    destruct (IHev1 ann_t1 H1 sub_lambda Σ' t1' tle H5) as [ann_v1 [v1' [k1 [tlt_l ev_l]]]].
    destruct (IHev2 ann_t2 H2 sub_arg Σ' t2' tle H8) as [ann_v2 [v2' [k2 [tlt_v2 ev_v2]]]].
    inversion tlt_l. subst.
    assert (tlt_sb : translatesTo remap_env (to_fresh_map Σ') [] 
      (csubst a' 0 b) (annot_csubst ann_v2 0 ann_b) (BigStepPIR.subst x' v2' b')).
    { eapply csubst_correct; auto. simpl. admit. }
    eapply (tlt_in_sub remap_env eΣ Σ' ann_env) in tlt_sb as sub_sb; try assumption.
    specialize (IHev3 (annot_csubst ann_v2 0 ann_b) sub_sb sub_v Σ' (BigStepPIR.subst x' v2' b') tle tlt_sb).
    destruct IHev3 as [ann_v' [v' [k3 [tlt_v ev_v]]]].
    exists ann_v'. exists v'. eexists. split.
    + apply tlt_v.
    + rewrite unfold_app_subst_entries. eapply E_Apply.
      * eexists.
      * apply ev_l.
      * apply ev_v2.
      * (* apply ev_v. *) admit.
  - (* let *)
    inversion tlt. apply inj_pair2 in H8. subst.
    eapply val_in_sub in ev1 as sub_br; eauto.
    destruct (IHev1 ann_br H1 sub_br Σ' br' tle H10) as [ann_v1 [v1' [k1 [tlt_br ev_br]]]].
    assert (tlt_sb : translatesTo remap_env (to_fresh_map Σ') [] 
      (csubst b0' 0 b1) (annot_csubst ann_v1 0 ann_b) (BigStepPIR.subst x'0 v1' b')).
    { eapply csubst_correct; auto. admit. }
    eapply (tlt_in_sub remap_env eΣ Σ' ann_env) in tlt_sb as sub_sb; try assumption.
    specialize (IHev2 (annot_csubst ann_v1 0 ann_b) sub_sb sub_v Σ' (subst x'0 v1' b') tle tlt_sb).
    destruct IHev2 as [ann_v' [v' [k2 [tlt_v ev_v]]]].
    exists ann_v'. exists v'. eexists. split.
    + apply tlt_v.
    + destruct Σ'.
      * simpl in *. econstructor. econstructor; simpl; eauto. 
      * destruct e as [e_kn [[vd ty] e_b']]. subst.
        erewrite unfold_let_subst_entries. simpl. admit.
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
    assert (decl = decl0 /\ body = cb) by eauto using declared_constant_same.
    invs H3. clear H0. clear H1.
    inversion tlt. subst.
    destruct (lookup_init eΣ Σ' ann_env c kn' decl0 cb isdecl e H1 tle) as [Σ'' [ann_cb [cb' tlt_cb]]].
    (* declarations may be evaluated under a subset of the environment *)
    assert (Σ'' = (to_fresh_map Σ')). { admit. } subst.
    destruct (IHev ann_cb H2 sub_v Σ' cb' tle tlt_cb) as [ann_v' [v' [k [tl_v' ev_v']]]].
    eexists. eexists. eexists. split.
    + eapply tl_v'.
    + (* will need to prove this under [Σ'1 ++ entry :: Σ'2] or by careful induction on the environment *) admit.
  - (* mkApps constr *)
    eapply val_in_sub in ev1 as sub_apps; eauto.
    apply mkApps_in_subset in sub_apps as [sub_constr _].
    inversion sub_constr.
  - (* atoms applied to values *)
    subst. induction f16; inversion H1.
    + inversion ev1. subst. inversion i.
    + rewrite List.nth_error_nil in H0. discriminate H0.
    + inversion ev1. subst. inversion i.
    + subst. (* apply LetIn to value *) 
      inversion tlt. subst.
      inversion H4. subst.
      inversion ev1.
      * subst. 
        (* let proof again *) admit.
      * subst. inversion H.
    + subst. (* apply proof again *) admit.
    + subst. (* const proof again *) admit.
 (* Atoms *)
  - subst. inversion tlt. exists ann. exists t''.
    subst. eexists. split. 
    + apply tlt_tt. 
    + admit. (* apply E_Constant. eauto. *)
  - (* rel *) subst. inversion i.
  - (* lambda *) subst. exists ann_t. exists t''. inversion tlt. 
    subst. eexists. split. 
    + apply tlt. 
    + admit.
    (* + apply E_LamAbs. eauto. *) 
Admitted.

Theorem stlc_no_globals : forall
  t (ann_t : annots box_type t) t' v,
  [] e⊢ t ⇓ v ->
  InSubset [] [] t ->
  translate_term remap_env [] [] t ann_t = Some t' ->
  exists ann_v v' k,
    translatesTo remap_env [] [] v ann_v v' /\
    eval t' v' k.
Proof with (eauto using eval).
  intros t ann_t t' v ev sub_t tlt.
  eapply (stlc_globals_correct [] tt [] t);
  try discriminate; eauto. constructor.
Qed.

Lemma eval_let_subst_entries_equiv : forall Σ' t' v' k,
  eval (subst_entries Σ' t') v' k ->
  exists j, eval (Let (map snd Σ') t') v' j.
Proof.
  induction Σ'; intros.
  - eauto.
  - destruct a as [a_kn [[a_kn' a_ty'] a_b']].
    simpl in *. rewrite subst_entries_comm in H; [|admit].
    apply IHΣ' in H. destruct H. eexists.
    constructor. econstructor; try eauto.
    + admit.
    + admit.
Admitted.

Lemma eval_binding_subst_entries_equiv : forall Σ' t' v' k,
  eval (subst_entries (List.rev Σ') t') v' k ->
  exists j,
    eval (bind_pir_env Σ' t') v' j.
Proof.
  intros. unfold bind_pir_env in *. 
  now eapply eval_let_subst_entries_equiv.
Qed.

Lemma let_binding_env_correct : forall eΣ Σ' t ann_t t' v ann_v v' j,
  (trans_env eΣ) e⊢ t ⇓ v ->
  translatesTo remap_env (to_fresh_map (List.rev Σ')) [] t ann_t t' /\
  eval (subst_entries (List.rev Σ') t') v' j ->
  exists (k : nat),
    translatesTo remap_env [] [] v ann_v v' /\ 
    eval (bind_pir_env Σ' t') v' k.
Admitted.

Theorem stlc_program_correct : forall eΣ ann_env init cb t v t',
  EGlobalEnv.declared_constant (trans_env eΣ) init cb ->
  cb.(cst_body) = Some t ->
  (trans_env eΣ) e⊢ t ⇓ v ->
  EnvInSubset eΣ ->
  translate_typed_eprogram remap_env ((eΣ; ann_env), init) = Ok t' ->
  exists ann_v v' k,
    translatesTo remap_env [] [] v ann_v v' /\
    eval t' v' k.
Proof.
  intros. unfold translate_typed_eprogram in H3.
  destruct (translate_env remap_env eΣ ann_env) as [Σ'|] eqn:tle; try discriminate.
  destruct (lookup_entry Σ' init) as [entry|] eqn:Hl; try discriminate.
  destruct entry as [e_kn [[vd ty'] b']]. inversion H3. subst.
  evar (ann_t : annots box_type t). eexists ?[ann_v]. eexists ?[v'].
  eapply let_binding_env_correct; try eauto.
  specialize (stlc_globals_correct eΣ ann_env (List.rev Σ') t ann_t (bind_pir_env Σ' (Var vd)) v H1 H2).
  (* translateEnv is reversed compared to the term *) admit.
Admitted.
