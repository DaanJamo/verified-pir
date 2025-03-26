From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Utils Require Import MCList.
From MetaCoq.Utils Require Import MCPrelude.
From VTL Require Import Env.
From VTL Require PIR.

From Coq Require Import String BinInt List.
From Coq Require Import Basics.

Local Open Scope string_scope.

Import Kernames ListNotations.

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

(* Since we don't remap to string we have to use two maps *)
Definition remap_fun (kn : kername) (df : PIR.DefaultFun) :=
  (kn, PIR.Builtin df).

Import BasicAst EAst.

(* TODO: extend with context to get fresh variable names *)
Definition get_name (na : name) : string :=
  match na with
  | nAnon => "a"
  | nNamed nm => if nm =? "_" then "a" else nm
  end.

Definition get_type (TT : env PIR.ty) : box_type -> PIR.ty :=
  fix go (bt : box_type) :=
match bt with
| TBox => PIR.Ty_Builtin (PIR.DefaultUniUnit)
| TArr dom codom => PIR.Ty_Fun (go dom) (go codom)
| TConst kn => let cst := string_of_kername kn in
    with_default (PIR.UNDEFINED "NotInMap") (lookup TT cst)
| TAny => PIR.UNDEFINED "UnknownType"
| _ => PIR.UNDEFINED "NotImplemented"
end.

(* translation based on ConCerts cameLIGO extraction *)
Fixpoint translate_term (TT : env PIR.ty) (t : term) 
                        {struct t} : annots box_type t -> PIR.term :=
match t return annots box_type t -> PIR.term with
| tVar n => fun bt => PIR.Var n
| tLambda na body => fun '(bt, a) =>
  let na' := get_name na in (* get fresh name from context? *)
  let (dom_tys, _) := ExAst.decompose_arr bt in
  let dom_ty := match nth_error dom_tys 0 with
                | Some ty => get_type TT ty
                | None => PIR.UNDEFINED "TypeNotInDomain"
                end in
      PIR.LamAbs na' dom_ty (translate_term TT body a) (* extend context *)
| tApp t1 t2 => fun '(bt, (T1, T2)) => 
    PIR.Apply (translate_term TT t1 T1) (translate_term TT t2 T2) (* fails for multiple arguments *)
| _ => fun _ => PIR.Var "notSupported"
end.

(* For now, we pass manual annotations until I set up a proper pipeline *)

Definition identity_EAst : term :=
  tLambda (nNamed (s_to_bs "x")) 
    (tVar (s_to_bs "x")).

Definition ann_id :=
  (TArr (TConst <%% Z %%>) (TConst <%% Z %%>), (TConst <%% Z %%>)).

Check ann_id.

Check (translate_term remap_env identity_EAst).
(* Eval cbv in <%% Z %%>. *)
Eval cbv in (translate_term remap_env identity_EAst ann_id).
