From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure Require Import EAst EAstUtils.
From MetaCoq.Utils Require Import MCList MCString MCPrelude.

From VTL Require Import Env PIR.

From Coq Require Import String BinInt List.

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
Fixpoint translate_term (TT : env PIR.ty) (ctx : context) (t : term) 
                        {struct t} : annots box_type t -> PIR.term :=
  match t return annots box_type t -> PIR.term with
  | tBox => fun bt => PIR.Constant (ValueOf DefaultUniUnit tt) (* boxes become the constructor of the [unit] type *)
  | tRel n => fun bt =>
    match nth_error ctx n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => PIR.Error (PIR.UNDEFINED ("Anonymous (" ++ string_of_nat n ++ ")"))
      | nNamed id => PIR.Var id
      end
    | None => PIR.Error (PIR.UNDEFINED ("UnboundRel(" ++ string_of_nat n ++ ")"))
    end
  | tLambda na body => fun '(bt, a) =>
      match ExAst.decompose_arr bt with
      | ([], _) => PIR.Error (PIR.UNDEFINED "LambdaTypeIsNotAFunction")
      | (ty :: _, _) =>
        match get_type TT ty with
        | PIR.UNDEFINED _ => PIR.Error (PIR.UNDEFINED "TypeNotDefined")
        | ty' => let na' := get_name na in (* get fresh name from context *)
          LamAbs na' ty' (translate_term TT (vass (nNamed (s_to_bs na')) :: ctx) body a) 
        end
      end
  | tApp t1 t2 => fun '(bt, (T1, T2)) => 
      PIR.Apply (translate_term TT ctx t1 T1) (translate_term TT ctx t2 T2) (* fails for multiple arguments *)
  | _ => fun _ => PIR.Error (PIR.UNDEFINED "NotSupported")
  end.

(* When the translation becomes more complicated, we might need to recurse *)
Fixpoint isError pt : Prop :=
  match pt with
  | PIR.Error _ => True
  | PIR.LamAbs _ _ b => isError b
  | PIR.Apply pt1 pt2 => isError pt1 /\ isError pt2 
  | _ => False
  end.

(* Lambda Box T is the combination of an EAst term with a dependent tree of its types
  For now, we pass manual annotations until I set up a proper pipeline *)

Definition identity_EAst : term :=
  tLambda (nNamed (s_to_bs "y")) 
    (tRel 0).

Definition ann_id :=
  (TArr (TConst <%% Z %%>) (TConst <%% Z %%>), (TConst <%% Z %%>)).

Eval cbv in (translate_term remap_env nil identity_EAst ann_id).
