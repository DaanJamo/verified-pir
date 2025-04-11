From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure Require Import EAst EAstUtils.
From MetaCoq.Utils Require Import MCList MCString MCPrelude utils.

From VTL Require Import Env PIR.

From Coq Require Import String BinInt List.

Local Open Scope string_scope.

Import Kernames ListNotations.
Import MCMonadNotation.

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).
Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.

Definition remap_ty (kn : kername) (uni : PIR.DefaultUni) := 
  (bs_to_s (string_of_kername kn), PIR.Ty_Builtin uni).

(* Look at integer and nat types in PIR *)
Definition remap_env : env PIR.ty :=
  [
    remap_ty <%% Z    %%> (PIR.DefaultUniInteger);
    remap_ty <%% unit %%> (PIR.DefaultUniUnit);
    remap_ty <%% bool %%> (PIR.DefaultUniBool)
  ].

Definition remap_fun (kn : kername) (df : PIR.DefaultFun) :=
  (kn, PIR.Builtin df).

Import BasicAst EAst.

(* TODO: extend with context to get fresh variable names *)
Definition get_name (na : name) : string :=
  match na with
  | nAnon => "a"
  | nNamed nm => if nm =? "_" then "a" else nm
  end.

Definition get_type (TT : env PIR.ty) : box_type -> option PIR.ty :=
  fix go (bt : box_type) :=
  match bt with
  | TBox => Some (PIR.Ty_Builtin (PIR.DefaultUniUnit))
  | TArr dom codom => 
    ty1 <- go dom ;;
    ty2 <- go codom ;;
    Some (PIR.Ty_Fun ty1 ty2)
  | TConst kn => lookup TT (string_of_kername kn)
  | _ => None
  end.

(* translate to option term with welltyped subset *)
(* proof that welltyped => some t *)
(* use var approach of malf? *)
Fixpoint translate_term (TT : env PIR.ty) (ctx : context) (t : term) 
                        {struct t} : annots box_type t -> option PIR.term :=
  match t return annots box_type t -> option PIR.term with
  | tBox => fun b_ty => Some (PIR.Constant (ValueOf DefaultUniUnit tt)) (* temporary constant *)
  | tRel n => fun b_ty =>
    match nth_error ctx n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => None
      | nNamed id => Some (PIR.Var id)
      end
    | None => None
    end
  | tLambda na bt => fun '(b_ty, a) =>
      match ExAst.decompose_arr b_ty with
      | ([], _) => None
      | (ty :: _, _) =>
        ty' <- get_type TT ty ;;
        let na' := get_name na in (* get fresh name from context *)
        bpt <- (translate_term TT (vass (nNamed (s_to_bs na')) :: ctx) bt a) ;;
        Some (LamAbs na' ty' bpt)
      end
  | tApp t1 t2 => fun '(b_ty, (ty1, ty2)) => (* does not handle all arguments yet, eta expansion?*)
    pt1 <- translate_term TT ctx t1 ty1 ;;
    pt2 <- translate_term TT ctx t2 ty2 ;;
    Some (PIR.Apply pt1 pt2)
  | _ => fun _ => None
  end.

Lemma unfold_lamAbs TT ctx na bt b_ty a :
  translate_term TT ctx (tLambda na bt) (b_ty, a) = 
  match ExAst.decompose_arr b_ty with
  | ([], _) => None
  | (ty :: _, _) =>
    ty' <- get_type TT ty ;;
    let na' := get_name na in (* get fresh name from context *)
    bpt <- (translate_term TT (vass (nNamed (s_to_bs na')) :: ctx) bt a) ;;
    Some (LamAbs na' ty' bpt)
  end.
Proof.
  auto.
Qed.

Lemma unfold_app TT ctx t1 t2 b_ty ty1 ty2 pt1 pt2 : 
  translate_term TT ctx t1 ty1 = Some pt1 ->
  translate_term TT ctx t2 ty2 = Some pt2 ->
  translate_term TT ctx (tApp t1 t2) (b_ty, (ty1, ty2)) = Some (PIR.Apply pt1 pt2).
Proof.
  intros. simpl. now rewrite H, H0.
Qed.

Definition translate_unsafe ctx (t : term) (ann : annots box_type t) := 
  with_default (PIR.Error (PIR.UNDEFINED "TranslationFailed")) ((translate_term remap_env ctx t) ann).

(* Lambda Box T is the combination of an EAst term with a dependent tree of its types
  For now, we pass manual annotations until I set up a proper pipeline *)

Definition identity_EAst : term :=
  tLambda (nNamed (s_to_bs "y")) 
    (tRel 0).

Definition ann_id :=
  (TArr (TConst <%% Z %%>) (TConst <%% Z %%>), (TConst <%% Z %%>)).

Eval cbv in (translate_unsafe nil identity_EAst ann_id).
