From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure Require Import EAst EAstUtils.
From MetaCoq.Utils Require Import MCList MCString MCPrelude utils.

From VTL Require Import Env PIR.

From Coq Require Import String BinInt List.

Local Open Scope string_scope.

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
(* TODO: extend with context to get fresh variable names *)

Definition translate_ty : box_type -> option PIR.ty :=
  fix go (ty : box_type) :=
  match ty with
  | TBox => Some (PIR.Ty_Builtin (PIR.DefaultUniUnit))
  | TArr a b => 
    a' <- go a ;;
    b' <- go b ;;
    Some (PIR.Ty_Fun a' b')
  | TConst kn => lookup TT (string_of_kername kn)
  | _ => None
  end.

Fixpoint translate_term (ctx : list bs) (t : term) 
                        {struct t} : annots box_type t -> option PIR.term :=
  match t return annots box_type t -> option PIR.term with
  | tBox => fun b_ty => Some (PIR.Constant (ValueOf DefaultUniUnit tt)) (* temporary constant *)
  | tRel n => fun b_ty =>
    match nth_error ctx n with
    | Some id => Some (PIR.Var id)
    | None => None
    end
  | tLambda (nNamed x) t => fun '(ty, t_ty) =>
      match ty with
      | TArr a _ =>
        a' <- translate_ty a ;;
        t' <- translate_term (x :: ctx) t t_ty ;;
        Some (LamAbs x a' t')
      | _ => None
      end
  | tApp s t => fun '(_, (s_ty, t_ty)) =>
    s' <- translate_term ctx s s_ty ;;
    t' <- translate_term ctx t t_ty ;;
    Some (PIR.Apply s' t')
  | _ => fun _ => None
  end.

Inductive translatesTypeTo : box_type -> PIR.ty -> Prop :=
  | tlty_tt  : translatesTypeTo TBox (PIR.Ty_Builtin DefaultUniUnit)
  | tlty_fun : forall ty1 ty2 ty1' ty2',
      translatesTypeTo ty1 ty1' ->
      translatesTypeTo ty2 ty2' ->
      translatesTypeTo (TArr ty1 ty2) (PIR.Ty_Fun ty1' ty2')
  | tlty_kn  : forall kn ty',
      lookup TT (string_of_kername kn) = Some ty' ->
      translatesTypeTo (TConst kn) ty'.

Inductive translatesTo (ctx : list bs) : forall (t : term),
  annots box_type t -> PIR.term -> Prop :=
  | tlt_tt : forall ann, translatesTo ctx tBox ann (Constant (ValueOf DefaultUniUnit tt))
  | tlt_rel : forall n x ann, (* look at rel ordering *)
      nth_error ctx n = Some x ->
      translatesTo ctx (tRel n) ann (Var x)
  | tlt_lambda : forall x ty1 ty2 b ann_b ty1' b',
      translatesTypeTo ty1 ty1' ->
      translatesTo (x :: ctx) b ann_b b' ->
      translatesTo ctx (tLambda (nNamed x) b) ((TArr ty1 ty2), ann_b) (LamAbs x ty1' b')
  | tlt_app : forall t1 t2 t1' t2' ann_t1 ann_t2 ty,
      translatesTo ctx t1 ann_t1 t1' ->
      translatesTo ctx t2 ann_t2 t2' ->
      translatesTo ctx (tApp t1 t2) (ty, (ann_t1, ann_t2)) (PIR.Apply t1' t2').

Theorem translate_type_reflect : forall ty ty',
  translate_ty ty = Some ty' <-> translatesTypeTo ty ty'.
Proof.
  intros ty ty'; split.
  - revert ty'. induction ty; try discriminate; intros ty' tl_ty.
    + inversion tl_ty. apply tlty_tt. 
    + inversion tl_ty as [Hty].
      destruct (translate_ty ty1) as [ty1'|]; try discriminate.
      destruct (translate_ty ty2) as [ty2'|]; try discriminate.
      specialize (IHty1 ty1' eq_refl).
      specialize (IHty2 ty2' eq_refl).
      inversion Hty as [Hty'].
      apply (tlty_fun ty1 ty2 ty1' ty2' IHty1 IHty2).
    + inversion tl_ty as [Hl].
      apply tlty_kn. apply Hl.
  - intros tl_ty. induction tl_ty.
    + auto.
    + simpl. rewrite IHtl_ty1, IHtl_ty2. reflexivity.
    + auto.
Qed.

Theorem translate_reflect : forall ctx t t' (ann : annots box_type t),
  translate_term ctx t ann = Some t' <-> translatesTo ctx t ann t'.
Proof.
  split.
  - revert ctx t'. induction t; try discriminate; intros ctx t' tl_t.
    + inversion tl_t. apply tlt_tt.
    + inversion tl_t as [Ht].
      destruct (nth_error ctx n) eqn:El; try discriminate.
      inversion Ht as [Ht'].
      apply tlt_rel. apply El.
    + inversion tl_t as [Ht]. destruct na; try discriminate.
      destruct ann as [[] ann_b]; try discriminate.
      destruct (translate_ty dom) as [ty1'|] eqn:tl_ty; try discriminate.
      destruct (translate_term (i :: ctx) t ann_b) as [b'|] eqn:tl_b; try discriminate.
      inversion Ht as [Ht']. subst.
      specialize (IHt ann_b (i :: ctx) b' tl_b).
      apply (translate_type_reflect dom ty1') in tl_ty.
      apply (tlt_lambda ctx i dom codom t ann_b ty1' b' tl_ty IHt).
    + inversion tl_t as [Ht].
      destruct ann as [ty [ann_t1 ann_t2]].
      destruct (translate_term ctx t1 ann_t1) as [t1'|] eqn:tl_t1; try discriminate.
      destruct (translate_term ctx t2 ann_t2) as [t2'|] eqn:tl_t2; try discriminate.
      inversion Ht as [Ht'].
      specialize (IHt1 ann_t1 ctx t1' tl_t1).
      specialize (IHt2 ann_t2 ctx t2' tl_t2).
      apply (tlt_app ctx t1 t2 t1' t2' ann_t1 ann_t2 ty IHt1 IHt2).
  - intros tl_t. induction tl_t.
    + auto.
    + simpl. rewrite H. reflexivity.
    + simpl. apply translate_type_reflect in H. rewrite H.
      simpl. setoid_rewrite IHtl_t. reflexivity.
    + simpl. rewrite IHtl_t1, IHtl_t2. reflexivity.
Qed.

End translate.

Definition translate_unsafe ctx (t : term) (ann : annots box_type t) := 
  with_default (PIR.Error (PIR.UNDEFINED "TranslationFailed")) (translate_term remap_env ctx t ann).

(* Lambda Box T is the combination of an EAst term with a dependent tree of its types
  For now, we pass manual annotations until I set up a proper pipeline *)
Definition identity_EAst : term :=
  tLambda (nNamed (s_to_bs "y")) 
    (tRel 0).

Definition ann_id :=
  (TArr (TConst <%% Z %%>) (TConst <%% Z %%>), (TConst <%% Z %%>)).

Eval cbv in (identity_EAst, ann_id).
Eval cbv in (translate_unsafe nil identity_EAst ann_id).
