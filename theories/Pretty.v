From Coq Require Import String BinInt List.

(* afaik Coq has no builtin string conversion methods
for its primitive types so we import the ones from QuickChick *)
(* but MetaCoq does! rewrite incoming *)
From QuickChick Require Import Show.
Import ShowFunctions.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

From VTL Require Import PIR.

Definition parens : string -> string :=
  fun x => "(" ++ x ++ ")"
.

Definition brackets : string -> string :=
  fun x => "[" ++ x ++ "]"
.

Definition braces : string -> string :=
  fun x => "{" ++ x ++ "}"
.

Definition arrow : string -> string -> string :=
  fun x y => x ++ " -> " ++ y
.

Definition sep (strs : list string) : string :=
  string_concat (intersperse " " strs)
.

Definition sepr (sp : string) (strs : list string) : string :=
  string_concat (intersperse sp strs)
.

(* TODO: improve span *)
Definition sexp (op : string) (strs : list string) : string :=
  "(" ++ op ++ " " (*++ newline*) ++ sep strs (*++ newline*) ++ ")"
.

Definition show_parens {A : Type} `{Show A} (x : A) : string :=
  parens (show x)
.

Definition show_sep {A : Type} `{Show A} (xs : list A) : string :=
  sep (map show xs)
.

Definition show_sexp {A : Type} `{Show A} (op : string) (xs : list A) : string :=
  sexp op (map show xs)
.

(* Definition show_rec (rec : recursivity ) : string :=
  match rec with
  | NonRec => "nonrec"
  | Rec    => "rec" 
  end
.

#[global]
Instance ShowRec : Show recursivity :=
{|
  show := show_rec
|}.

Definition show_strict (st : strictness) : string :=
  match st with
  | NonStrict => "nonstrict"
  | Strict    => "strict" 
  end
.

#[global]
Instance ShowStrict : Show strictness :=
{|
  show := show_strict
|}. *)


Definition show_DefaultUni (U : DefaultUni) : string :=
  match U with
  | DefaultUniInteger => "integer"
  (*| DefaultUniByteString => "bytestring" (*!*)
  | DefaultUniString => "string" (*!*)*)
  | DefaultUniUnit => "unit"
  | DefaultUniBool => "bool"
  (*| DefaultUniProtoList => "list" (* ! *)
  | DefaultUniProtoPair => "pair" (* ! *)
  | DefaultUniData => "data"
  | DefaultUniBLS12_381_G1_Element => "bls12_381_G1_element"
  | DefaultUniBLS12_381_G2_Element => "bls12_381_G2_element"
  | DefaultUniBLS12_381_MlResult => "bls12_381_mlresult"

  | DefaultUniApply U1 U2 =>
      sep [show_DefaultUni U1 ; show_DefaultUni U2] (*!*)*)
  end
.

#[global]
Instance ShowDefaultUni : Show DefaultUni :=
{|
  show := show_DefaultUni
|}.

Definition show_Constant (cst : constant) : string :=
  let val := match cst with
  (* | ValueOf uni val => sep [show uni ; show val] end in 
  (* is it possible to infer show for each unitype like the above? *) *)
  | ValueOf DefaultUniInteger z => show_Z z
  (* | ValueOf DefaultUniByteString bs => "NotImplemented:bs"
  | ValueOf DefaultUniString str => "NotImplemented:str" *)
  | ValueOf DefaultUniUnit u => "unit"
  | ValueOf DefaultUniBool b => show_bool b end in
  (* | ValueOf DefaultUniProtoList Us => "NotImplemented:protolist"
  | ValueOf DefaultUniProtoPair Us => "NotImplemented:protopair"
  | ValueOf DefaultUniData d => "NotImplemented:data"
  | ValueOf DefaultUniBLS12_381_G1_Element z => show_Z z
  | ValueOf DefaultUniBLS12_381_G2_Element z => show_Z z
  | ValueOf DefaultUniBLS12_381_MlResult z => show_Z z
  | ValueOf (DefaultUniApply U1 U2) U => "NotImplemented:apply" end in *)
  sep [match cst with (ValueOf uni _) => show uni end ; val]
.

#[global]
Instance ShowConstant : Show constant :=
{|
  show := show_Constant
|}.

(* TODO: copy all the other functions *)
Definition show_DefaultFun (df : DefaultFun) : string :=
  match df with
  | AddInteger => "addInteger"
  | SubtractInteger => "subtractInteger"
  | MultiplyInteger => "multiplyInteger"
  | DivideInteger => "divideInteger"
  | QuotientInteger => "quotientInteger"
  | RemainderInteger => "remainderInteger"
  | ModInteger => "modInteger"
  | EqualsInteger => "equalsInteger"
  | LessThanInteger => "lessThanInteger"
  | LessThanEqualsInteger => "lessThanEqualsInteger"
  (* | _ => "UnknownDefaultFunction" *)
  end
.

#[global]
Instance ShowDefaultFun : Show DefaultFun :=
{|
  show := show_DefaultFun
|}.

(* Do we have datakinds? the plc pretty-printer does something with (type) here *)
(*Fixpoint show_kind (k : kind) : string :=
  match k with
  | Kind_Base => "*"
  | Kind_Arrow k1 k2 => sexp "fun" [show_kind k1 ; show_kind k2] (*!*) 
  end
.

#[global]
Instance ShowKind : Show kind :=
{|
  show := show_kind
|}.*)

Fixpoint show_ty (T : ty) : string :=
  match T with
  (*| Ty_Var tn => sep [tn] (*!*)*)
  | Ty_Fun T1 T2 => sexp "fun" [show_ty T1 ; show_ty T2] (*!*)
  (*| Ty_IFix T1 T2 => sexp "ifix" [show_ty T1 ; show_ty T2] (*!*)
  | Ty_Forall btn k T => sexp "all" [btn ; show k ; show_ty T] (*!*)*)
  | Ty_Builtin U => sexp "con" [show U]
  | UNDEFINED err => braces err 
  (*| Ty_Lam btn k T => sexp "lam" [btn ; show k ; show_ty T] (*!*)
  | Ty_App T1 T2 => brackets (sep [show_ty T1 ; show_ty T2]) (*!*)*)
  end
.

#[global]
Instance ShowTy : Show ty :=
{|
  show := show_ty
|}.

(*Definition show_vdecl (vd : vdecl) : string :=
  match vd with
  | VarDecl bn T => sexp "vardecl" [bn ; show T]
  end
.

#[global]
Instance ShowVDecl : Show vdecl :=
{|
  show := show_vdecl
|}.

Definition show_tvdecl (tvd : tvdecl) : string :=
  match tvd with
  | TyVarDecl btn k => sexp "tyvardecl" [btn ; show_parens k]
  end
.

#[global]
Instance ShowTVDecl : Show tvdecl :=
{|
  show := show_tvdecl
|}.

Definition show_dtdecl (dtd : dtdecl) : string :=
  match dtd with
  | Datatype tvd tvds bn vds => sexp "datatype" [
    show tvd ; show_sep tvds ;
    bn ; show vds] (*!*)
  end
.

#[global]
Instance ShowDTDecl : Show dtdecl :=
{|
  show := show_dtdecl
|}.*)

Fixpoint show_term (t : term) : string :=
  match t with
  (* | Let rec bds t => sexp "let" [show_parens rec ;
      sep (map show_binding bds) ; show_term t] *)
  | Var x => sep [x]
  (* | TyAbs bn k t => sexp "abs" [bn ; show k ; show_term t] *)
  | LamAbs x T t => sexp "lam" [x  ; show T ; show_term t]
  | Apply t1 t2 => brackets (sep [show_term t1 ; show_term t2])
  | Constant cst => sexp "con" [show cst]
  | Builtin def => sexp "builtin" [show def]
  (* | TyInst t T => braces (sep [show_term t ; show T]) *)
  | Error T => sexp "error" [show T]
  (* | IWrap T1 T2 t => sexp "iwrap" [show T1 ; show T2 ; show_term t] *)
  (* | Unwrap t => sexp "unwrap" [show_term t] *)
  (* | Constr T n ts => sexp "consr" [show T ; show n ; sep (map show_term ts)] *)
  (* | Case T t ts => sexp "case" [show T ; show_term t ; sep (map show_term ts)] *)
  end

(* with show_binding (b : binding) : string := 
  match b with
  | TermBind strc vdecl t => sexp "termbind" [
      show strc ; show vdecl ; show_term t]
  | TypeBind tvdecl T => sexp "typebind" [show tvdecl ; show T]
  | DatatypeBind dtdecl => sexp "datatypebind" [show dtdecl]
  end *)
.

#[global]
Instance ShowTerm : Show term :=
{|
  show := show_term
|}.

Definition print_as_program (t : term) :=
  sexp "program" ["1.1.0" ; show t]
.

(* Eval cbv in (print_as_program (LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x"))). *)
