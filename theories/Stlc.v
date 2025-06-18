From Coq Require Import Strings.String List Nat.
Import ListNotations.

From VTL Require Import PIR BigStepPIR.

Module STLC.

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

Lemma app_cons_comm : forall {A} Γ1 Γ2 (x : A),
  (Γ1 ++ x :: Γ2) = (Γ1 ++ [x] ++ Γ2).
Proof.
  induction Γ1; auto.
Qed.

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
  | ntl_rel : forall n x, nth_error Γ n = Some x -> translatesToNamed Γ (ntm_rel n) (Var x)
  | ntl_abs : forall x x' ty ty' b b',
      ~ In x' Γ (* or bound_vars *) ->
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
    + now apply nth_error_Some_length, ltb_lt in H0.
    + simpl. apply nth_error_In in H0.
      apply existsb_exists. exists x. 
      split. apply H0. now apply String.eqb_eq.
  - simpl. destruct (IHt1 Γ t1' H1), (IHt2 Γ t2' H3). auto.
  - destruct (IHt (x' :: Γ) b' H5). simpl. auto.
  - auto.
  - auto.
Qed.

Lemma not_in_cons_r : forall (x a : string) Γ,
  x <> a /\ ~ (In x Γ) ->
  ~ (In x (Γ ++ [a])).
Proof.
  intros x a Γ [Hneq HnIn].
  unfold not. intros Hin. rewrite in_app_iff in Hin.
  destruct Hin.
  - contradiction.
  - simpl in H. destruct H.
    + symmetry in H. contradiction.
    + apply H.
Qed.

Fixpoint bound_vars t' : list string :=
  match t' with
  | LamAbs x ty b' => x :: bound_vars b'
  | Apply t1' t2' => bound_vars t1' ++ bound_vars t2'
  | _ => []
  end.

Lemma not_in_bound_vars_app : forall x t1' t2',
  ~ In x (bound_vars (Apply t1' t2')) ->
  ~ In x (bound_vars t1') /\ ~ In x (bound_vars t2').
Proof.
  intros x t1' t2' nIn. simpl in nIn. rewrite in_app_iff in nIn.
  apply Decidable.not_or in nIn. assumption.
Qed.

Lemma not_in_bound_vars_abs : forall x x' ty' b',
  ~ In x (bound_vars (LamAbs x' ty' b')) ->
  x <> x' /\ ~ In x (bound_vars b').
Proof.
  intros x x' ty' b' nIn. simpl in nIn.
  apply Decidable.not_or in nIn as [nIn1 nIn2].
  auto.
Qed.

Lemma weaken_ctx : forall Γ x t t',
  ~ In x (bound_vars t') ->
  translatesToNamed Γ t t' ->
  translatesToNamed (Γ ++ [x]) t t'.
Proof.
  intros Γ' x' t. revert Γ' x'.
  induction t; intros Γ x t' nIn tlt_t;
  inversion tlt_t.
  - apply ntl_rel. now apply (nth_error_app_left).
  - subst. apply not_in_bound_vars_app in nIn as [nIn1 nIn2].
    specialize (IHt1 Γ x t1' nIn1 H1).
    specialize (IHt2 Γ x t2' nIn2 H3).
    apply ntl_app. apply IHt1. apply IHt2.
  - subst. apply not_in_bound_vars_abs in nIn as [Hx Hinb].
    specialize (IHt (x' :: Γ) x b' Hinb H5).
    apply ntl_abs; try assumption. 
    apply not_in_cons_r. auto.
  - apply ntl_true.
  - apply ntl_false.
Qed.

Lemma weaken_ctx_many : forall Γ1 Γ2 t t',
  (forall x, In x Γ2 -> ~ In x (bound_vars t')) ->
  translatesToNamed Γ1 t t' ->
  translatesToNamed (Γ1 ++ Γ2) t t'.
Proof.
  intros Γ1 Γ2 t. revert Γ1. induction t;
  intros Γ1 t' nIn tlt_t; inversion tlt_t.
  - apply ntl_rel. rewrite nth_error_app1.
    apply H0. apply nth_error_Some_length in H0. apply H0.
  (* how to simplify? *)
  - subst. apply ntl_app. 
    apply IHt1; try assumption.
    { intros x nIn1. apply nIn in nIn1.
      apply not_in_bound_vars_app in nIn1 as [nIn1 _].
      assumption. }
    apply IHt2; try assumption.
    { intros x nIn2. apply nIn in nIn2.
      apply not_in_bound_vars_app in nIn2 as [_ nIn2].
      assumption. }
  - subst. apply ntl_abs.
    assert (HnIn2 : ~ In x' Γ2).
    { 
      unfold not. intros Hin. apply nIn in Hin.
      apply Decidable.not_or in Hin as [Hcontra _].
      contradiction.
    }
    rewrite in_app_iff. unfold not. intros. 
    destruct H; contradiction. assumption.
    assert (HnInb : forall x : string, In x Γ2 -> ~ In x (bound_vars b')).
    {
      intros. apply nIn in H.
      apply not_in_bound_vars_abs in H.
      apply H.
    }
    apply (IHt (x' :: Γ1) b' HnInb H5).
  - apply ntl_true.
  - apply ntl_false.
Qed.

Lemma weaken_closedUnder : forall (Γ : list string) x t',
  closedUnder Γ t' ->
  closedUnder (Γ ++ [x]) t'.
Proof.
  intros Γ' x t'. revert Γ'. induction t'; intros Γ H.
  - simpl in *. 
    rewrite (existsb_app (fun v : string => v =? n) Γ [x]).
    now rewrite H.
  - simpl in *. apply (IHt' (b :: Γ) H).
  - inversion H. apply andb_true_iff in H1 as [Ht1 Ht2].
    specialize (IHt'1 Γ Ht1). specialize (IHt'2 Γ Ht2).
    simpl. auto.
  - auto.
  - auto.
  - discriminate.
Qed.

Lemma nth_error_outer_binder : forall {A} (Γ : list A) x,
  nth_error (Γ ++ [x]) (List.length Γ) = Some x.
Proof.
  intros.
  rewrite nth_error_app2, sub_diag.
  auto. apply le_refl.
Qed.

Lemma nth_error_not_bound : forall {A} (Γ : list A) x x' n,
  List.length Γ <> n ->
  nth_error (Γ ++ [x]) n = Some x' ->
  n < List.length Γ.
Proof.
  intros.
  apply nth_error_Some_length in H0.
  rewrite length_app in H0. simpl in H0.
  lia.
Qed.

Lemma tlt_n_length : forall Γ k t',
  translatesToNamed Γ (ntm_rel k) t' ->
  k < List.length Γ.
Proof. 
  intros Γ k t' tlt.
  inversion tlt.
  now apply nth_error_Some_length in H0.
Qed.

Lemma in_not_in : forall {A} (l : list A) (x x' : A),
  In x l ->
  ~ In x' l ->
  x <> x'.
Proof.
  unfold not. intros.
  subst. contradiction.
Qed.

Lemma tlt_NoDup : forall (Γ : list string) n x x',
  ~ In x Γ ->
  nth_error (Γ ++ [x]) n = Some x' ->
  n < List.length Γ ->
  x <> x'.
Proof.
  intros. rewrite nth_error_app1 in H0; [|assumption].
  apply nth_error_In in H0. 
  symmetry. apply (in_not_in Γ); assumption.
Qed.

Lemma csubst_correct : forall Γ k x v b v' b',
  k = #|Γ| ->
  ~ In x Γ ->
  translatesToNamed nil v v' ->
  translatesToNamed (Γ ++ [x]) b b' ->
  translatesToNamed Γ <{[k :-> v] b}> (BigStepPIR.subst x v' b').
Proof.
  intros Γ k' x v b. revert Γ k'. induction b;
  intros Γ k v' b' Hk nIn ntl_v ntl_b;
  inversion ntl_b.
  - simpl. destruct (k =? n)%nat eqn:En.
    + apply eqb_eq in En. subst. 
      rewrite nth_error_outer_binder in H0.
      inversion H0. rewrite String.eqb_refl.
      apply (weaken_ctx_many nil Γ) in ntl_v.
      apply ntl_v. (* forall, ~ In x1 (bound_vars v')*) admit.
    + subst. destruct (x =? x0) eqn:Ex.
      * apply String.eqb_eq in Ex. apply eqb_neq in En.
        apply nth_error_not_bound in H0 as Hl. 2: apply En.
        assert (Hcontra : x <> x0).
        apply (tlt_NoDup Γ n); assumption.
        apply (weaken_ctx_many nil Γ) in ntl_v; [|auto].
        contradiction.
      * apply eqb_neq in En.
        assert (n < #|Γ|). apply (nth_error_not_bound Γ x x0).
        apply En. apply H0. rewrite nth_error_app1 in H0.
        apply ntl_rel. apply H0. apply H.
  - specialize (IHb1 Γ k v' t1' Hk nIn ntl_v H1).
    specialize (IHb2 Γ k v' t2' Hk nIn ntl_v H3).
    simpl. apply ntl_app. apply IHb1. apply IHb2.
  - assert (Hl : S k = List.length (x' :: Γ)). simpl. auto.
    (* TODO: clean this up *)
    simpl. destruct (x =? x') eqn:Exb.
    { apply String.eqb_eq in Exb. rewrite in_app_iff in H2.
      apply Decidable.not_or in H2 as [_ Hcontra]. simpl in Hcontra.
      unfold not in Hcontra. destruct Hcontra. auto.
    }
    assert (~ In x (x'::Γ)). apply not_in_cons. apply String.eqb_neq in Exb. 
    auto. specialize (IHb (x' :: Γ) (S k) v' b'0 Hl H6 ntl_v H5).
    apply ntl_abs. rewrite in_app_iff in H2. apply Decidable.not_or in H2 as [Hx' _].
    apply Hx'. assumption. (* closedUnder *) admit.
  - apply ntl_true.
  - apply ntl_false.
Admitted.

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
    apply (csubst_correct [] 0 x' v2 b v2' b'). 
    reflexivity. apply H4. assumption. simpl. apply H7.
    destruct (IHevn3 (BigStepPIR.subst x' v2' b') Hs) as [v' [k3 [ntl_s ev_s]]].
    exists v'. eexists. split. apply ntl_s. eapply E_Apply. eexists.
    apply ev_l. apply ev_v2. apply ev_s.
  - exists t'. eexists. subst...
  - exists t'. eexists. subst...
Qed.

End nameless.
