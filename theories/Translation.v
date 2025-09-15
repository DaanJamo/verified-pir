From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure Require Import EAst EAstUtils.
From MetaCoq.Utils Require Import MCList MCString MCPrelude utils.

From VTL Require Import Env PIR Utils.

From Coq Require Import String BinInt List.

Import Kernames ListNotations.
Import MCMonadNotation.
Import BasicAst EAst.

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).
Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.

Definition remap_ty (kn : kername) (uni : PIR.DefaultUni) := 
  (bs_to_s (string_of_kername kn), PIR.Ty_Builtin uni).

Definition remap_env : env PIR.ty :=
  [
    remap_ty <%% Z    %%> (PIR.DefaultUniInteger);
    remap_ty <%% unit %%> (PIR.DefaultUniUnit);
    remap_ty <%% bool %%> (PIR.DefaultUniBool)
  ].

Definition remap_fun (kn : kername) (df : PIR.DefaultFun) :=
  (kn, PIR.Builtin df).

Section translate.

Context (TT : env PIR.ty).

Definition gen_fresh_name na Γ :=
  match na with
  | nAnon => gen_fresh "anon" Γ
  | nNamed id => gen_fresh id Γ
  end.

Definition translate_ty : box_type -> option PIR.ty :=
  fix go (ty : box_type) :=
  match ty with
  | TBox => Some (PIR.Ty_Builtin (PIR.DefaultUniUnit))
  | TArr a b => 
    a' <- go a ;;
    b' <- go b ;;
    Some (PIR.Ty_Fun a' b')
  | TInd ind => lookup TT (string_of_kername ind.(inductive_mind))
  | _ => None
  end.

Fixpoint translate_term (Γ : list string) (t : term) 
                        {struct t} : annots box_type t -> option PIR.term :=
  match t return annots box_type t -> option PIR.term with
  | tBox => fun b_ty => Some (PIR.Constant (ValueOf DefaultUniUnit tt)) (* temporary constant *)
  | tRel n => fun b_ty =>
    match nth_error Γ n with
    | Some id => Some (PIR.Var id)
    | None => None
    end
  | tLambda x b => fun '(ty, ann_b) =>
    match ty with
    | TArr br_ty _ =>
      let x' := gen_fresh_name x Γ in
      br_ty' <- translate_ty br_ty ;;
      b' <- translate_term (x' :: Γ) b ann_b ;;
      Some (LamAbs x' br_ty' b')
    | _ => None
    end
  | tLetIn x br b => fun '(ty, (ann_br, ann_b)) =>
    match ty with
    | TArr br_ty _ =>
      let x' := gen_fresh_name x Γ in
      br_ty' <- translate_ty br_ty ;; 
      br' <- translate_term Γ br ann_br ;;
      b' <- translate_term (x' :: Γ) b ann_b ;;
      Some (Let [TermBind (VarDecl x' br_ty') br'] b')
    | _ => None
    end
  | tApp f a => fun '(_, (ann_f, ann_a)) =>
    f' <- translate_term Γ f ann_f ;;
    a' <- translate_term Γ a ann_a ;;
    Some (Apply f' a')
  | _ => fun _ => None
  end.

Inductive translatesTypeTo : box_type -> PIR.ty -> Prop :=
  | tlty_tt : translatesTypeTo TBox (PIR.Ty_Builtin DefaultUniUnit)
  | tlty_fun : forall ty1 ty2 ty1' ty2',
      translatesTypeTo ty1 ty1' ->
      translatesTypeTo ty2 ty2' ->
      translatesTypeTo (TArr ty1 ty2) (PIR.Ty_Fun ty1' ty2')
  | tlty_ind : forall ind ty',
      lookup TT (string_of_kername ind.(inductive_mind)) = Some ty' ->
      translatesTypeTo (TInd ind) ty'.

Inductive translatesTo (Γ : list string) : forall (t : term),
  annots box_type t -> PIR.term -> Prop :=
  | tlt_tt : forall ann, translatesTo Γ tBox ann (Constant (ValueOf DefaultUniUnit tt))
  | tlt_rel : forall n x ann,
      find_index_string Γ x = Some n ->
      translatesTo Γ (tRel n) ann (Var x)
  | tlt_lambda : forall x x' arg_ty res_ty b ann_b arg_ty' b',
      translatesTypeTo arg_ty arg_ty' ->
      translatesTo (x' :: Γ) b ann_b b' ->
      translatesTo Γ (tLambda x b) (TArr arg_ty res_ty, ann_b) (LamAbs x' arg_ty' b')
  | tlt_let : forall x x' br_ty b_ty br b ann_br ann_b br_ty' br' b',
      translatesTypeTo br_ty br_ty' ->
      translatesTo Γ br ann_br br' ->
      translatesTo (x' :: Γ) b ann_b b' ->
      translatesTo Γ (tLetIn x br b) (TArr br_ty b_ty, (ann_br, ann_b)) (Let [(TermBind (VarDecl x' br_ty') br')] b')
  | tlt_app : forall t1 t2 ann_t1 ann_t2 ty t1' t2',
      translatesTo Γ t1 ann_t1 t1' ->
      translatesTo Γ t2 ann_t2 t2' ->
      translatesTo Γ (tApp t1 t2) (ty, (ann_t1, ann_t2)) (PIR.Apply t1' t2').

Theorem translate_type_reflect : forall ty ty',
  translate_ty ty = Some ty' -> translatesTypeTo ty ty'.
Proof.
  intros ty ty'. revert ty'. induction ty; try discriminate; 
  intros ty' tl_ty; inversion tl_ty.
    + apply tlty_tt.
    + destruct (translate_ty ty1) as [ty1'|]; [|discriminate].
      destruct (translate_ty ty2) as [ty2'|]; [|discriminate].
      specialize (IHty1 ty1' eq_refl).
      specialize (IHty2 ty2' eq_refl).
      inversion H0 as [Hty'].
      now eapply tlty_fun.
    + now apply tlty_ind.
Qed.

Theorem translate_reflect : forall Γ t t' (ann : annots box_type t),
  NoDup Γ ->
  translate_term Γ t ann = Some t' -> translatesTo Γ t ann t'.
Proof.
  intros Γ t. revert Γ. induction t; try discriminate; 
  intros Γ t' ann nodup tl_t; inversion tl_t as [Ht].
  - apply tlt_tt.
  - destruct (nth_error Γ n) eqn:El; [|discriminate].
    inversion Ht as [Ht']. apply tlt_rel. 
    now apply nth_error_to_find_index in El. 
  - destruct ann as [[] ann_b]; try discriminate.
    destruct (translate_ty dom) as [br_ty'|] eqn:tl_ty; [|discriminate].
    destruct (translate_term (gen_fresh_name na Γ :: Γ) t ann_b) as [b'|] eqn:tl_b; [|discriminate].
    inversion Ht as [Ht']. assert (nodup' : NoDup (gen_fresh_name na Γ :: Γ)).
    apply NoDup_cons; try assumption. 
    unfold gen_fresh_name. destruct na; apply gen_fresh_fresh.
    specialize (IHt (gen_fresh_name na Γ :: Γ) b' ann_b nodup' tl_b).
    apply (translate_type_reflect dom br_ty') in tl_ty.
    now apply tlt_lambda.
  - destruct ann as [[] [ann_br ann_b]]; try discriminate.
    destruct (translate_ty dom) as [br_ty'|] eqn:tl_ty; [|discriminate].
    destruct (translate_term Γ t1 ann_br) as [br'|] eqn:tl_br; [|discriminate].
    destruct (translate_term (gen_fresh_name na Γ :: Γ) t2 ann_b) as [b'|] eqn:tl_b; [|discriminate].
    inversion Ht as [Ht']. assert (nodup' : NoDup (gen_fresh_name na Γ :: Γ)).
    apply NoDup_cons; try assumption.
    unfold gen_fresh_name. destruct na; apply gen_fresh_fresh.
    specialize (IHt1 Γ br' ann_br nodup tl_br).
    specialize (IHt2 (gen_fresh_name na Γ :: Γ) b' ann_b nodup' tl_b).
    apply (translate_type_reflect dom br_ty') in tl_ty.
    now apply tlt_let.
  - destruct ann as [ty [ann_t1 ann_t2]].
    destruct (translate_term Γ t1 ann_t1) as [t1'|] eqn:tl_t1; [|discriminate].
    destruct (translate_term Γ t2 ann_t2) as [t2'|] eqn:tl_t2; [|discriminate].
    inversion Ht as [Ht'].
    specialize (IHt1 Γ t1' ann_t1 nodup tl_t1).
    specialize (IHt2 Γ t2' ann_t2 nodup tl_t2).
    now apply tlt_app.
Qed.

End translate.

Definition translate_unsafe Γ (t : term) (ann : annots box_type t) := 
  with_default (PIR.Error (PIR.UNDEFINED "TranslationFailed")) (translate_term remap_env Γ t ann).

(* Lambda Box T is the combination of an EAst term with a dependent tree of its types
  For now, we pass manual annotations until I set up a proper pipeline *)
Definition identity_EAst : term :=
  tLambda (nNamed (s_to_bs "y")) 
    (tRel 0).

Definition let_test : term :=
  tLetIn (nNamed "x") tBox (tApp identity_EAst (tRel 1)).

Definition Z_ind := TInd (mkInd <%% Z %%> 0).
Definition ann_id :=
  (TArr Z_ind Z_ind, Z_ind).

Eval cbv in (identity_EAst, ann_id).
Eval cbv in (translate_unsafe nil identity_EAst ann_id).

Eval cbv in (translate_unsafe nil let_test, (Z_ind, Z_ind, ann_id)).
