From Coq Require Import Strings.String List Nat.
Import ListNotations.

From VTL Require Import PIR BigStepPIR.

(* Named STLC from Software Foundations extended
  with an invalid term/type to test partial translation,
  plus a proof that this translation preserves semantics.*)
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

Reserved Notation "s '==>' t" (at level 91, left associativity).

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

(* Translation relations allow us to keep the actual implementation
  abstract and focus on the evaluation rules. We then define a lemma
  that shows that our translation adheres to the relation. *)
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
