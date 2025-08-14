From Coq Require Import Strings.String List Nat.
Import ListNotations.

From VTL Require Export PIR BigStepPIR Utils.

(* More difficult translation from a nameless STLC that uses De Bruijn
indices and a context to PIR, similar to the main proof as λ□ is also nameless *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_ERROR : ty.

Inductive tm : Type :=
  | tm_rel   : nat -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_oops  : tm.

From MetaCoq.Utils Require Import utils.
Import MCMonadNotation.

Import Strings.String Nat.
Local Open Scope string_scope.

Fixpoint translate_type ty : option PIR.ty :=
  match ty with
  | Ty_Bool => Some (PIR.Ty_Builtin DefaultUniBool)
  | Ty_Arrow ty1 ty2 => 
      ty1' <- translate_type ty1 ;;
      ty2' <- translate_type ty2 ;;
      Some (PIR.Ty_Fun ty1' ty2') 
  | Ty_ERROR => None
  end.

Fixpoint translate_term (Γ : list string) tm : option term :=
  match tm with
  | tm_rel k => 
      match nth_error Γ k with
      | Some x => Some (Var x)
      | None => None end
  | tm_app tm1 tm2 => 
    tm1' <- translate_term Γ tm1 ;;
    tm2' <- translate_term Γ tm2 ;;
    Some (Apply tm1' tm2')
  | tm_abs x ty b =>
      let x' := (gen_fresh x Γ) in
      ty' <- translate_type ty ;;
      b' <- translate_term (x'::Γ) b ;;
      Some (LamAbs x' ty' b')
  | tm_true => Some (Constant (ValueOf DefaultUniBool true))
  | tm_false => Some (Constant (ValueOf DefaultUniBool false))
  | tm_oops => None 
  end.

Definition translate_unsafe t := 
  match translate_term [] t with
  | Some t' => t'
  | None => Error (UNDEFINED "translation error")
  end.

Fixpoint csubst k s t : tm :=
  match t with
  | tm_rel n => if (k =? n)%nat then s else tm_rel n
  | tm_app t1 t2 => tm_app (csubst k s t1) (csubst k s t2)
  | tm_abs x T b => tm_abs x T (csubst (S k) s b)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_oops => tm_oops end.

Inductive eval : tm -> tm -> Prop :=
  | EN_Abs : forall x T b,
      eval (tm_abs x T b) (tm_abs x T b)
  | EN_App : forall t1 t2 x ty b v2 v,
      eval t1 (tm_abs x ty b) ->
      eval t2 v2 ->
      eval (csubst 0 v2 b) v ->
      eval (tm_app t1 t2) v
  | EN_True  : eval tm_true tm_true
  | EN_False : eval tm_false tm_false.

Inductive translatesTypeTo : ty -> PIR.ty -> Prop :=
  | tlty_bool  : translatesTypeTo Ty_Bool (PIR.Ty_Builtin DefaultUniBool)
  | tlty_arrow : forall ty1 ty2 ty1' ty2',
      translatesTypeTo ty1 ty1' ->
      translatesTypeTo ty2 ty2' ->
      translatesTypeTo (Ty_Arrow ty1 ty2) (PIR.Ty_Fun ty1' ty2').

Inductive translatesTo (Γ : list string) : tm -> term -> Prop :=
  | tlt_rel : forall n x, 
      find_index_string Γ x = Some n -> 
      translatesTo Γ (tm_rel n) (Var x)
  | tlt_abs : forall x x' ty ty' b b',
      translatesTypeTo ty ty' ->
      translatesTo (x' :: Γ) b b' ->
      translatesTo Γ (tm_abs x ty b) (LamAbs x' ty' b')
  | tlt_app : forall t1 t2 t1' t2',
      translatesTo Γ t1 t1' ->
      translatesTo Γ t2 t2' ->
      translatesTo Γ (tm_app t1 t2) (Apply t1' t2')
  | tlt_true : translatesTo Γ tm_true (Constant (ValueOf DefaultUniBool true))
  | tlt_false : translatesTo Γ tm_false (Constant (ValueOf DefaultUniBool false)).

Theorem translate_type_reflect : forall ty ty',
  translate_type ty = Some ty' <-> translatesTypeTo ty ty'.
Proof.
  intros ty ty'; split.
  - revert ty'. induction ty; intros ty' tl_ty.
    + inversion tl_ty. apply tlty_bool.
    + inversion tl_ty as [Hty].
      destruct (translate_type ty1) as [ty1'|]; [|discriminate].
      destruct (translate_type ty2) as [ty2'|]; [|discriminate].
      specialize (IHty1 ty1' Logic.eq_refl).
      specialize (IHty2 ty2' Logic.eq_refl).
      inversion Hty as [Hty']. 
      apply (tlty_arrow ty1 ty2 ty1' ty2' IHty1 IHty2).
    + discriminate.
  - intros tl_ty. induction tl_ty.
    + auto.
    + simpl. rewrite IHtl_ty1, IHtl_ty2. reflexivity.
Qed.

(* NoDup -> no shadowing up to now *)
Theorem tl_in_tlt : forall Γ t t',
  NoDup Γ ->
  translate_term Γ t = Some t' -> translatesTo Γ t t'.
Proof.
  intros Γ t. revert Γ. induction t;
  intros Γ t' nodup tl; inversion tl.
  - destruct (nth_error Γ n) eqn:Hnth; [|discriminate].
    inversion H0. apply tlt_rel.
    now apply nth_error_to_find_index in Hnth.
  - destruct (translate_term Γ t1) eqn:Ht1; [|discriminate].
    destruct (translate_term Γ t2) eqn:Ht2; [|discriminate].
    inversion H0.
    specialize (IHt1 Γ t0 nodup Ht1).
    specialize (IHt2 Γ t3 nodup Ht2).
    now apply tlt_app.
  - destruct (translate_type t0) eqn:Hty; [|discriminate].
    destruct (translate_term (gen_fresh s Γ :: Γ) t1) eqn:Hb; [|discriminate].
    inversion H0. assert (Hnodup' : NoDup (gen_fresh s Γ :: Γ)).
    apply NoDup_cons. apply gen_fresh_fresh. assumption.
    specialize (IHt ((gen_fresh s Γ)::Γ) t3 Hnodup' Hb).
    apply translate_type_reflect in Hty as Hty'.
    now apply tlt_abs.
  - apply tlt_true.
  - apply tlt_false.
Qed.

Lemma weaken_ctx : forall Γ x t t',
  translatesTo Γ t t' ->
  translatesTo (Γ ++ [x]) t t'.
Proof.
  intros Γ' x' t. revert Γ' x'.
  induction t; intros Γ x t' tlt_t;
  inversion tlt_t; subst.
  - apply tlt_rel. now apply find_index_weaken.
  - apply tlt_app. 
    apply IHt1. apply H1.
    apply IHt2. apply H3.
  - specialize (IHt (x' :: Γ) x b' H4).
    apply tlt_abs; assumption.
  - apply tlt_true.
  - apply tlt_false.
Qed.

Lemma weaken_ctx_many : forall Γ1 Γ2 t t',
  translatesTo Γ1 t t' ->
  translatesTo (Γ1 ++ Γ2) t t'.
Proof.
  intros Γ1 Γ2 t. revert Γ1. induction t;
  intros Γ1 t' tlt_t; inversion tlt_t; subst.
  - apply tlt_rel. now apply find_index_weaken.
  - apply tlt_app.
    apply IHt1; assumption.
    apply IHt2; assumption.
  - apply tlt_abs. assumption.
    now apply (IHt (x' :: Γ1)). 
  - apply tlt_true.
  - apply tlt_false.
Qed.

Lemma csubst_shadowed : forall Γ x b b' v,
  In x Γ ->
  translatesTo (Γ ++ [x]) b b' ->
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
  translatesTo (Γ ++ [x]) b b' ->
  translatesTo Γ b b'.
Proof.
  intros Γ x b. revert Γ. induction b;
  intros Γ b' Hin tlt; inversion tlt; subst.
  - apply tlt_rel.
    unfold find_index_string in H0.
    destruct_str_eq x x0.
    + subst. now rewrite find_index_app1 in H0.
    + rewrite find_index_app1 in H0. auto.
      now eapply find_index_not_outer.
  - apply tlt_app.
    apply IHb1; assumption.
    apply IHb2; assumption.
  - apply tlt_abs. assumption.
    apply IHb. now right. assumption.
  - apply tlt_true.
  - apply tlt_false.
Qed.

Lemma csubst_correct : forall Γ x v b v' b',
  ~ In x Γ ->
  translatesTo nil v v' ->
  translatesTo (Γ ++ [x]) b b' ->
  translatesTo Γ (csubst (List.length Γ) v b) (BigStepPIR.subst x v' b').
Proof.
  intros Γ x v b. revert Γ. induction b;
  intros Γ v' b' HnIn tlt_v tlt_b;
  inversion tlt_b.
  - subst. simpl. destruct_str_eq x x0.
    + subst. apply find_index_outer_length in H0 as Hl; auto.
      symmetry in Hl. apply eqb_eq in Hl. rewrite Hl.
      now eapply weaken_ctx_many in tlt_v.
    + apply find_index_not_outer in H0 as Hin; auto.
      apply find_index_not_outer_length in H0 as Hl; auto.
      unfold find_index_string in H0.
      rewrite find_index_app1 in H0; auto. rewrite Hl.
      now apply tlt_rel.
  - simpl. apply tlt_app.
    apply IHb1; assumption.
    apply IHb2; assumption.
  - subst. simpl. destruct_str_eq x x'.
    + subst x'. apply tlt_abs. assumption.
      assert (Hin : In x (x::Γ)). now left.
      specialize (strengthen_shadowed_ctx (x :: Γ) x b b'0 Hin H4) as Hctx.
      specialize (csubst_shadowed (x :: Γ) x b b'0 v Hin H4) as H1.
      simpl in H1. now rewrite H1.
    + apply tlt_abs; try assumption.
      apply IHb; auto. now apply not_in_cons.
  - apply tlt_true.
  - apply tlt_false.
Qed.

Theorem translate_correct : forall t v t',
  eval t v ->
  translate_term [] t = Some t' ->
  exists v' k,
    translatesTo [] v v' /\
    BigStepPIR.eval t' v' k.
Proof with (eauto using BigStepPIR.eval).
  intros t v t'' evn tl. apply tl_in_tlt in tl; try apply NoDup_nil. 
  revert t'' tl; induction evn; intros t' tlt; inversion tlt.
  - exists t'. eexists. subst...
  - subst.
    destruct (IHevn1 t1' H1) as [v1' [k1 [tlt_l ev_l]]].
    destruct (IHevn2 t2' H3) as [v2' [k2 [nln_v2 ev_v2]]].
    inversion tlt_l. subst.
    assert (Hs : translatesTo [] (csubst 0 v2 b) (BigStepPIR.subst x' v2' b')).
    apply (csubst_correct [] x' v2 b v2' b'); auto.
    destruct (IHevn3 (BigStepPIR.subst x' v2' b') Hs) as [v' [k3 [tlt_s ev_s]]].
    exists v'. eexists. split. apply tlt_s. eapply E_Apply. eexists.
    apply ev_l. apply ev_v2. apply ev_s.
  - exists t'. eexists. subst...
  - exists t'. eexists. subst...
Qed.
