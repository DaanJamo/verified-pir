From Coq Require Import Strings.String List Nat.
Import ListNotations.

From VTL Require Import PIR BigStepPIR Utils.

(* Named STLC from Software Foundations extended
with a wrong term/type to test partial translation *)
Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_ERROR : ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_oops  : tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "ty1 -> ty2" := (Ty_Arrow ty1 ty2) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc_tm at level 0).
Notation "'OOPS'" := tm_oops (in custom stlc_tm at level 0).

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

(* Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x ty2 t1,
      value <{\x:ty2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:ty, t1}> =>
      if String.eqb x y then t else <{\y:ty, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{OOPS}> =>
      <{OOPS}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Reserved Notation "s '==>' t" (at level 90, left associativity).

Inductive eval : tm -> tm -> Prop :=
  | E_Val : forall v,
    value v ->
    eval v v
  | E_App : forall t1 t2 x ty b v2 v,
    ty <> Ty_ERROR ->
    t1 ==> <{\x : ty, b}> ->
    t2 ==> v2 ->
    <{[x := v2] b}> ==> v ->
    <{t1 t2}> ==> v

where "s '==>' t" := (eval s t).

Hint Constructors eval : core.

(* Simpler translation to experiment with the form of the main proof,
first from a STLC with named variables to PIR which is also named *)
From MetaCoq.Utils Require Import utils.
Import MCMonadNotation.

Fixpoint translate_type ty : option PIR.ty :=
  match ty with
  | Ty_Bool => Some (PIR.Ty_Builtin DefaultUniBool)
  | Ty_Arrow ty1 ty2 => 
      ty1' <- translate_type ty1 ;;
      ty2' <- translate_type ty2 ;;
      Some (PIR.Ty_Fun ty1' ty2') 
  | Ty_ERROR => None
  end.

Fixpoint translate tm : option term :=
  match tm with
  | tm_var x => Some (Var x)
  | tm_app tm1 tm2 => 
    tm1' <- translate tm1 ;;
    tm2' <- translate tm2 ;;
    Some (Apply tm1' tm2')
  | tm_abs x ty b =>
    ty' <- translate_type ty ;; 
    b' <- translate b ;;
    Some (LamAbs x ty' b')
  | tm_true => Some (Constant (ValueOf DefaultUniBool true))
  | tm_false => Some (Constant (ValueOf DefaultUniBool false))
  | tm_oops => None 
  end.

Ltac solve_pir_eval := split; [(eexists ; eauto using BigStepPIR.eval) | constructor].

Lemma tl_lambda : forall x ty b t',
  translate <{\x : ty, b}> = Some t' ->
  exists b' ty',
    translate_type ty = Some ty' /\
    translate b = Some b' /\
    LamAbs x ty' b' = t'.
Proof.
  intros x ty b t' tl_t.
  inversion tl_t as [Ht].
  destruct (translate_type ty) as [ty'|]; try discriminate.
  destruct (translate b) as [b'|]; try discriminate.
  inversion Ht as [Ht'].
  exists b'. exists ty'. auto.
Qed.

Lemma tl_lambda' : forall x ty b ty' b',
  translate_type ty = Some ty' ->
  translate b = Some b' ->
  translate <{\x:ty, b}> = Some (LamAbs x ty' b').
Proof.
  intros. simpl. rewrite H, H0. reflexivity.
Qed.

Lemma tl_app : forall t1 t2 t',
  translate <{t1 t2}> = Some t' ->
  exists t1' t2',
    translate t1 = Some t1' /\
    translate t2 = Some t2' /\
    Apply t1' t2' = t'.
Proof.
  intros t1 t2 t' tl_t. inversion tl_t as [Ht].
  destruct (translate t1) as [t1'|]; try discriminate.
  destruct (translate t2) as [t2'|]; try discriminate.
  inversion Ht.
  exists t1'. exists t2'. auto.
Qed.

Lemma tl_app' : forall t1 t2 t1' t2',
  translate t1 = Some t1' ->
  translate t2 = Some t2' ->
  translate <{t1 t2}> = Some (Apply t1' t2').
Proof.
  intros t1 t2 t1' t2' tl_t1 tl_t2.
  simpl. rewrite tl_t1. rewrite tl_t2.
  reflexivity.
Qed.

Lemma subst_same : forall x v b v' b',
  translate v = Some v' ->
  translate b = Some b' ->
  translate <{[x := v] b}> = Some (BigStepPIR.subst x v' b').
Proof.
  intros x v b.
  induction b; intros v' b' tl_v tl_b.
  - inversion tl_b. simpl in *. 
    destruct (x =? s)%string; auto.
  - apply tl_app in tl_b.
    destruct tl_b as [t1' [t2' [tl_t1 [tl_t2 eqt]]]].
    subst. simpl.
    rewrite (IHb1 v' t1' tl_v tl_t1).
    rewrite (IHb2 v' t2' tl_v tl_t2).
    reflexivity.
  - apply tl_lambda in tl_b.
    destruct tl_b as [b'' [ty' [tl_ty [tl_b eqb]]]]. 
    subst. simpl. destruct (x =? s)%string.
    + simpl. rewrite tl_ty, tl_b. reflexivity.
    + simpl. rewrite tl_ty. rewrite (IHb v' b'' tl_v tl_b).
      reflexivity.
  - inversion tl_b. auto.
  - inversion tl_b. auto.
  - discriminate.
Qed.

Theorem translate_correct : forall t v t',
  eval t v ->
  translate t = Some t' ->
  exists v' k,
    translate v = Some v' /\
    BigStepPIR.eval t' v' k.
Proof with (eauto using BigStepPIR.eval).
  intros t v t' ev. revert t'. 
  induction ev. intros t' tl_t.
  - destruct H. 
    + apply tl_lambda in tl_t.
      destruct tl_t as [b' [ty' [tl_ty [tl_b eq_b]]]].
      eexists. eexists. split.
      * simpl. rewrite tl_ty, tl_b. reflexivity.
      * rewrite <- eq_b...
    + inversion tl_t. simpl...
    + inversion tl_t. simpl...
  - intros ta' tl_ta. apply tl_app in tl_ta.
    destruct tl_ta as [t1' [t2' [tl_t1 [tl_t2 tl_a]]]].
    destruct (IHev1 t1' tl_t1) as [lv' [k1 [tl_l step1]]].
    destruct (IHev2 t2' tl_t2) as [v2' [k2 [tl_v2 step2]]].
    apply tl_lambda in tl_l.
    destruct tl_l as [b' [ty' [tl_ty [tl_b eq_b]]]].
    assert (Hs: translate <{ [x := v2] b }> = Some (BigStepPIR.subst x v2' b')).
    apply (subst_same x v2 b v2' b' tl_v2 tl_b).
    destruct (IHev3 (BigStepPIR.subst x v2' b') Hs) as [v' [k3 [tl_v step3]]].
    exists v'. exists (k1 + k2 + 1 + k3). split. apply tl_v. subst.
    eapply E_Apply. eauto. apply step1. apply step2. apply step3.
Qed.

Inductive translatesTypeTo : ty -> PIR.ty -> Prop :=
  | tlty_bool  : translatesTypeTo Ty_Bool (PIR.Ty_Builtin DefaultUniBool)
  | tlty_arrow : forall ty1 ty2 ty1' ty2',
      translatesTypeTo ty1 ty1' ->
      translatesTypeTo ty2 ty2' ->
      translatesTypeTo (Ty_Arrow ty1 ty2) (PIR.Ty_Fun ty1' ty2').

Inductive translatesTo : tm -> term -> Prop :=
  | tlt_var : forall x, translatesTo (tm_var x) (Var x)
  | tlt_app : forall t1 t2 t1' t2', 
      translatesTo t1 t1' ->
      translatesTo t2 t2' ->
      translatesTo (tm_app t1 t2) (Apply t1' t2')
  | tlt_abs : forall x ty b ty' b', translatesTo b b' ->
      translatesTypeTo ty ty' ->
      translatesTo (tm_abs x ty b) (LamAbs x ty' b') 
  | tlt_true : translatesTo tm_true (Constant (ValueOf DefaultUniBool true))
  | tlt_false : translatesTo tm_false (Constant (ValueOf DefaultUniBool false)).

Theorem translate_type_reflect : forall ty ty',
  translate_type ty = Some ty' <-> translatesTypeTo ty ty'.
Proof.
  intros ty ty'; split.
  - revert ty'. induction ty; intros ty' tl_ty.
    + inversion tl_ty. apply tlty_bool.
    + inversion tl_ty as [Hty].
      destruct (translate_type ty1) as [ty1'|]; try discriminate.
      destruct (translate_type ty2) as [ty2'|]; try discriminate.
      specialize (IHty1 ty1' eq_refl).
      specialize (IHty2 ty2' eq_refl).
      inversion Hty as [Hty']. 
      apply (tlty_arrow ty1 ty2 ty1' ty2' IHty1 IHty2).
    + discriminate.
  - intros tl_ty. induction tl_ty.
    + auto.
    + simpl. rewrite IHtl_ty1, IHtl_ty2. reflexivity.
Qed.  

Theorem translate_reflect : forall t t',
  translate t = Some t' <-> translatesTo t t'.
Proof. 
  split.
  - revert t'. induction t; intros t' tl_t.
    + inversion tl_t. apply (tlt_var s).
    + apply tl_app in tl_t.
      destruct tl_t as [t1' [t2' [tl_t1 [tl_t2 eqt]]]].
      specialize (IHt1 t1' tl_t1).
      specialize (IHt2 t2' tl_t2).
      rewrite <- eqt.
      apply (tlt_app t1 t2 t1' t2' IHt1 IHt2).
    + apply tl_lambda in tl_t.
      destruct tl_t as [b' [ty' [tl_ty [tl_b eq_l]]]].
      rewrite <- eq_l.
      apply (tlt_abs s t t0 ty' b' (IHt b' tl_b)).
      apply translate_type_reflect in tl_ty. apply tl_ty.
    + inversion tl_t. apply tlt_true.
    + inversion tl_t. apply tlt_false.
    + discriminate.
  - intros tlt_t. induction tlt_t.
    + auto.
    + apply tl_app'.
      apply IHtlt_t1. apply IHtlt_t2.
    + apply tl_lambda'. apply translate_type_reflect in H.
      apply H. apply IHtlt_t.
    + auto.
    + auto.
Qed.

Theorem translatesTo_correct : forall t v t',
  eval t v ->
  translatesTo t t' ->
  exists v' k,
    translatesTo v v' /\
    BigStepPIR.eval t' v' k.
Proof with (eauto using BigStepPIR.eval).
  intros t v t' ev. revert t'.
  induction ev. intros t' tlt_t.
  - induction H; inversion tlt_t; exists t'; eexists.
    + split; [apply tlt_t| subst; eauto using BigStepPIR.eval].
    + split; [apply tlt_t| subst; eauto using BigStepPIR.eval].
    + split; [apply tlt_t| subst; eauto using BigStepPIR.eval].
  - intros t' tlt_t.
    inversion tlt_t. subst.
    destruct (IHev1 t1' H2) as [lv' [k1 [tlt_l ev_l]]].
    destruct (IHev2 t2' H4) as [v2' [k2 [tlt_v2 ev_v2]]].
    inversion tlt_l.
    assert (Hs: translate <{ [x := v2] b }> = Some (BigStepPIR.subst x v2' b')).
    apply translate_reflect in tlt_v2 as tl_v2.
    apply translate_reflect in H6 as tl_b.
    apply (subst_same x v2 b v2' b' tl_v2 tl_b).
    apply translate_reflect in Hs as tlt_s.
    destruct (IHev3 (BigStepPIR.subst x v2' b') tlt_s) as [v' [k3 [tlt_v ev_v]]].
    exists v'. exists (k1 + k2 + 1 + k3). split. apply tlt_v.
    eapply E_Apply. eauto. rewrite <- H3 in ev_l. apply ev_l. apply ev_v2. apply ev_v.
Qed.

(* More difficult translation from a nameless STLC that uses De Bruijn
indices and a context to PIR, similar to the main proof as λ□ is also nameless *)
Section nameless.

Import Strings.String Nat.
Local Open Scope string_scope.

Fixpoint gen_fresh_aux x (Γ : list string) n :=
  match n with
  | 0 => x
  | S n' => let x' := x ++ "'" in 
      if existsb (Strings.String.eqb x') Γ then gen_fresh_aux x' Γ n' else x'
  end.

Definition gen_fresh x (Γ : list string) :=
  gen_fresh_aux x Γ #|Γ|.

Lemma gen_fresh_fresh x (Γ : list string) :
  ~ (In (gen_fresh x Γ) Γ).
Proof.
  unfold gen_fresh.
Admitted.

Inductive ntm : Type :=
  | ntm_rel   : nat -> ntm
  | ntm_app   : ntm -> ntm -> ntm
  | ntm_abs   : string -> ty -> ntm -> ntm
  | ntm_true  : ntm
  | ntm_false : ntm
  | ntm_oops  : ntm.

Fixpoint lift n k nt : ntm :=
  match nt with
  | ntm_rel i => if Nat.leb k i then ntm_rel (n + i) else ntm_rel i
  | ntm_app t1 t2 => ntm_app (lift n k t1) (lift n k t2)
  | ntm_abs x T b => ntm_abs x T (lift n (S k) b)
  | ntm_true => ntm_true
  | ntm_false => ntm_false
  | ntm_oops => ntm_oops end.

Notation lift0 n := (lift n 0).
Definition up := lift 1 0.

Fixpoint closedn k nt : bool :=
  match nt with
  | ntm_rel i => Nat.ltb i k 
  | ntm_app t1 t2 => closedn k t1 && closedn k t2
  | ntm_abs x T b => closedn (S k) b
  | ntm_oops => false
  | _ => true end.

Notation closed t := (closedn 0 t).

Reserved Notation "'[' k ':->' s ']' t" (in custom stlc_tm at level 5, k global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint csubst k s t : ntm :=
  match t with
  | ntm_rel n => if (k =? n)%nat then s else ntm_rel n
  | ntm_app t1 t2 => ntm_app (csubst k s t1) (csubst k s t2)
  | ntm_abs x T b => ntm_abs x T (csubst (S k) s b)
  | ntm_true => ntm_true
  | ntm_false => ntm_false
  | ntm_oops => ntm_oops end

where "'[' k ':->' s ']' t" := (csubst k s t) (in custom stlc_tm).

Lemma csubst_closed k v t : closedn k t -> csubst k v t = t.
Proof.
  revert k. induction t; intros k' Hcl; inversion Hcl.
  - apply ltb_lt, lt_neq, neq_sym, eqb_neq in H0.
    simpl. rewrite H0. reflexivity.
  - apply andb_true_iff in H0 as [Hcl1 Hcl2]. simpl.
    rewrite (IHt1 k' Hcl1), (IHt2 k' Hcl2). reflexivity.
  - simpl. rewrite (IHt (S k') H0). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Inductive evalNamed : ntm -> ntm -> Prop :=
  | EN_Abs : forall x T b,
      evalNamed (ntm_abs x T b) (ntm_abs x T b)
  | EN_App : forall t1 t2 x ty b v2 v,
      evalNamed t1 (ntm_abs x ty b) ->
      evalNamed t2 v2 ->
      evalNamed (csubst 0 v2 b) v ->
      evalNamed (ntm_app t1 t2) v
  | EN_True  : evalNamed ntm_true ntm_true
  | EN_False : evalNamed ntm_false ntm_false.

Inductive translatesToNamed (Γ : list string) : ntm -> term -> Prop :=
  | ntl_rel : forall n x, 
      find_index Γ x = Some n -> 
      translatesToNamed Γ (ntm_rel n) (Var x)
  | ntl_abs : forall x x' ty ty' b b',
      translatesTypeTo ty ty' ->
      translatesToNamed (x' :: Γ) b b' ->
      translatesToNamed Γ (ntm_abs x ty b) (LamAbs x' ty' b')
  | ntl_app : forall t1 t2 t1' t2',
      translatesToNamed Γ t1 t1' ->
      translatesToNamed Γ t2 t2' ->
      translatesToNamed Γ (ntm_app t1 t2) (Apply t1' t2')
  | ntl_true : translatesToNamed Γ ntm_true (Constant (ValueOf DefaultUniBool true))
  | ntl_false : translatesToNamed Γ ntm_false (Constant (ValueOf DefaultUniBool false)).

Lemma tl_closed : forall Γ t t',
  translatesToNamed Γ t t' ->
    closedn #|Γ| t /\
    closedUnder Γ t'.
Proof.
  intros Γ' t. revert Γ'; induction t; 
  intros Γ t'' tlt_t; inversion tlt_t.
  - split.
    + now apply find_index_Some_length, ltb_lt in H0.
    + simpl. apply find_index_In in H0.
      apply existsb_exists. exists x.
      split. apply H0. now apply String.eqb_eq.
  - simpl. destruct (IHt1 Γ t1' H1), (IHt2 Γ t2' H3). auto.
  - destruct (IHt (x' :: Γ) b' H4). simpl. auto.
  - auto.
  - auto.
Qed.

Lemma weaken_ctx : forall Γ x t t',
  translatesToNamed Γ t t' ->
  translatesToNamed (Γ ++ [x]) t t'.
Proof.
  intros Γ' x' t. revert Γ' x'.
  induction t; intros Γ x t' tlt_t;
  inversion tlt_t; subst.
  - apply ntl_rel. now apply find_index_weaken.
  - apply ntl_app. 
    apply IHt1. apply H1.
    apply IHt2. apply H3.
  - specialize (IHt (x' :: Γ) x b' H4).
    apply ntl_abs; assumption.
  - apply ntl_true.
  - apply ntl_false.
Qed.

Lemma weaken_ctx_many : forall Γ1 Γ2 t t',
  translatesToNamed Γ1 t t' ->
  translatesToNamed (Γ1 ++ Γ2) t t'.
Proof.
  intros Γ1 Γ2 t. revert Γ1. induction t;
  intros Γ1 t' tlt_t; inversion tlt_t; subst.
  - apply ntl_rel. now apply find_index_weaken.
  - apply ntl_app.
    apply IHt1; assumption.
    apply IHt2; assumption.
  - apply ntl_abs. assumption.
    now apply (IHt (x' :: Γ1)). 
  - apply ntl_true.
  - apply ntl_false.
Qed.

Lemma csubst_shadowed : forall Γ x b b' v,
  In x Γ ->
  translatesToNamed (Γ ++ [x]) b b' ->
  csubst (List.length Γ) v b = b.
Proof.
  intros Γ x b. revert Γ. induction b; 
  intros Γ b' v Hin tlt; inversion tlt.
  - simpl.
    destruct_nat_eq (List.length Γ) n.
    + subst. apply find_index_outer in H0 as Hx.
      subst x. now apply find_index_outer_not_In in H0.
    + reflexivity.
  - simpl.
    rewrite (IHb1 Γ t1' v); try assumption.
    rewrite (IHb2 Γ t2' v); try assumption.
    reflexivity.
  - specialize (IHb (x' :: Γ) b'0 v).
    simpl in *. rewrite IHb; auto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma strengthen_shadowed_ctx : forall Γ x b b',
  In x Γ ->
  translatesToNamed (Γ ++ [x]) b b' ->
  translatesToNamed Γ b b'.
Proof.
  intros Γ x b. revert Γ. induction b;
  intros Γ b' Hin tlt; inversion tlt; subst.
  - apply ntl_rel. 
    destruct_str_eq x x0.
    + subst. now rewrite find_index_app1 in H0.
    + rewrite find_index_app1 in H0. auto.
      now eapply find_index_not_outer.
  - apply ntl_app.
    apply IHb1; assumption.
    apply IHb2; assumption.
  - apply ntl_abs. assumption.
    apply IHb. now right. assumption.
  - apply ntl_true.
  - apply ntl_false.
Qed.

Lemma subst_shadowed : forall Γ x b b' v',
  In x Γ ->
  translatesToNamed (Γ ++ [x]) b b' ->
  BigStepPIR.subst x v' b' = b'.
Proof.
  intros Γ x b b'. revert Γ b. induction b';
  intros Γ b'' v Hin tlt; inversion tlt; subst.
  - simpl. (* here we'd have to reason backwards to show that the same name
    would imply that a binder before this would have stopped substitution *) admit.
  - simpl. destruct_str_eq x b.
    + reflexivity.
    + f_equal. assert (In x (b :: Γ)) by now right. 
      now apply (IHb' (b :: Γ) b0). 
  - simpl.
    rewrite (IHb'1 Γ t1); try assumption.
    rewrite (IHb'2 Γ t2); try assumption.
    reflexivity.
  - reflexivity.
  - reflexivity.
Admitted.

Theorem csubst_rel_correct : forall Γ x y v v' k,
  translatesToNamed nil v v' ->
  translatesToNamed (Γ ++ [x]) (ntm_rel k) (Var y) ->
  translatesToNamed Γ (csubst (List.length Γ) v (ntm_rel k)) (BigStepPIR.subst x v' (Var y)).
Proof.
  intros Γ x y v v' k ntl_v ntl_b.
  inversion ntl_b.
  apply find_index_app_iff in H1 as Hshadowed.
  inversion Hshadowed.
  + apply find_index_shadowed_length in H1 as Hl; auto.
    destruct_str_eq x y.
    - subst.
      erewrite csubst_shadowed; eauto.
      (* There is a binder that has shadowed the variable we're substituting for:
         \y...\y...y so k refers to this second binder instead. PIR should have stopped
         substituting at this second binder so we couldn't have ended up here. *)
      erewrite subst_shadowed; eauto. (* this was an attempt to solve it similarly to csubst*)
      (* this isn't the right lemma yet*)
      now apply strengthen_shadowed_ctx in ntl_b.
    - simpl. rewrite Hl, Heqb.
      rewrite find_index_app1 in H1; auto.
      now apply ntl_rel.
  + simpl. destruct H2.
    apply find_index_outer_length in H1 as Hl; auto.
    subst. apply find_index_outer in H1 as Hx; auto.
    apply String.eqb_eq in Hx. rewrite eqb_refl, Hx.
    now eapply weaken_ctx_many in ntl_v.
Qed.

Lemma csubst_correct : forall Γ x v b v' b',
  translatesToNamed nil v v' ->
  translatesToNamed (Γ ++ [x]) b b' ->
  translatesToNamed Γ (csubst (List.length Γ) v b) (BigStepPIR.subst x v' b').
Proof.
  intros Γ x v b. revert Γ. induction b;
  intros Γ v' b' tlt_v tlt_b;
  inversion tlt_b.
  - subst b'. now apply csubst_rel_correct.
  - simpl. apply ntl_app.
    apply IHb1; assumption.
    apply IHb2; assumption.
  - subst. simpl. destruct_str_eq x x'.
    + subst x'. apply ntl_abs. assumption.
      assert (Hin : In x (x::Γ)). now left.
      specialize (strengthen_shadowed_ctx (x :: Γ) x b b'0 Hin H4) as Hctx.
      specialize (csubst_shadowed (x :: Γ) x b b'0 v Hin H4) as H1.
      simpl in H1. now rewrite H1.
    + apply ntl_abs; try assumption.
      apply IHb; auto.
  - apply ntl_true.
  - apply ntl_false.
Qed.

Theorem translate_correct_named : forall t v t',
  evalNamed t v ->
  translatesToNamed [] t t' ->
  exists v' k,
    translatesToNamed [] v v' /\
    BigStepPIR.eval t' v' k.
Proof with (eauto using BigStepPIR.eval).
  intros t v t'' evn. revert t''; induction evn; 
  intros t' tln_t; inversion tln_t.
  - exists t'. eexists. subst...
  - subst.
    destruct (IHevn1 t1' H1) as [v1' [k1 [ntl_l ev_l]]].
    destruct (IHevn2 t2' H3) as [v2' [k2 [nln_v2 ev_v2]]].
    inversion ntl_l. subst.
    assert (Hs : translatesToNamed [] (csubst 0 v2 b) (BigStepPIR.subst x' v2' b')).
    apply (csubst_correct [] x' v2 b v2' b'); auto.
    destruct (IHevn3 (BigStepPIR.subst x' v2' b') Hs) as [v' [k3 [ntl_s ev_s]]].
    exists v'. eexists. split. apply ntl_s. eapply E_Apply. eexists.
    apply ev_l. apply ev_v2. apply ev_s.
  - exists t'. eexists. subst...
  - exists t'. eexists. subst...
Qed.

Theorem allowed_shadowing Γ :
  let nt := ntm_abs "x" Ty_Bool 
              (ntm_abs "x" Ty_Bool (ntm_rel 0)) in
  let pt := LamAbs "x" (Ty_Builtin DefaultUniBool) 
              (LamAbs "x" (Ty_Builtin DefaultUniBool) (Var "x")) in
  translatesToNamed Γ nt pt.
Proof.
  intros. unfold nt, pt.
  apply ntl_abs. apply tlty_bool.
  apply ntl_abs. apply tlty_bool.
  apply ntl_rel. apply find_index_first.
Qed.

Theorem disallowed_shadowing Γ n :
  n > 0 ->
  let nt := ntm_abs "x" Ty_Bool 
              (ntm_abs "x" Ty_Bool (ntm_rel n)) in
  let pt := LamAbs "x" (Ty_Builtin DefaultUniBool) 
              (LamAbs "x" (Ty_Builtin DefaultUniBool) (Var "x")) in
  ~ translatesToNamed (Γ ++ ["x"]) nt pt.
Proof.
  unfold not. intros Hn tlt. 
  invs tlt. invs H6. invs H8. 
  apply find_index_Some_first in H3. 
  apply lt_neq, neq_sym in Hn. contradiction. 
Qed.

End nameless.
