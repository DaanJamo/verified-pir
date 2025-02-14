From MetaCoq.Common Require Import BasicAst.
Import bytestring.
From MetaCoq.Erasure Require Export EAst.
From VTL Require PIR.
From Coq Require Import String.

#[local] Open Scope string_scope.

Definition get_name (n : name) : string :=
  match n with
  | nAnon => "anon"
  | nNamed n => String.to_string n end
.

Fixpoint to_pir (t : term) : PIR.term :=
  match t with
  | tVar n => PIR.Var (String.to_string n)
  | tLambda n b => PIR.LamAbs (get_name n) 
    (PIR.Ty_Builtin (PIR.DefaultUniInteger)) (to_pir b)
  | tApp t1 t2 => PIR.App (to_pir t1) (to_pir t2)
  | _ => PIR.Var "undefined"
  end
.

Definition identity_EAst : term :=
  tLambda (nNamed (String.of_string "x")) 
    (tVar (String.of_string "x")).

Eval cbv in (to_pir identity_EAst).
