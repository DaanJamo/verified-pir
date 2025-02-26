From Coq.Strings Require Import String.
#[local] Open Scope string_scope.

From VTL Require Import PIR.

Definition parens : string -> string :=
  fun x => "(" ++ x ++ ")"
.

Definition brackets : string -> string :=
  fun x => "[" ++ x ++ "]"
.

Definition pretty_print_DefaultUni (D : DefaultUni) : string :=
  match D with
  | DefaultUniInteger => "integer"
  | DefaultUniBool => "bool"
  | DefaultUniUnit => "unit"
  end
.

Definition pretty_print_DefaultFun (F : DefaultFun) : string :=
  match F with
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
  end
.

Fixpoint pretty_print_ty (T : ty) : string :=
  match T with
  | Ty_Builtin D => "con " ++ pretty_print_DefaultUni D
  | Ty_Fun T1 T2 => pretty_print_ty T1 ++ " -> " ++ pretty_print_ty T2
  | UNDEFINED s => "ERROR: " ++ s
  end
.

Fixpoint pretty_print' (t : term) : string :=
  match t with
  | Var x => x
  | LamAbs x T t => parens (
      "lam " ++ x ++ " "
      ++ parens (pretty_print_ty T)
      ++ " " ++ (pretty_print' t)
    )
  | App t1 t2 => brackets (
    (pretty_print' t1) ++ " " 
    ++ pretty_print' t2)
  | Builtin def => parens ("builtin " ++ (pretty_print_DefaultFun def))
  | Constant T v => parens ((pretty_print_ty T) ++ " " ++ v)
  end
.

Definition print_as_program (t : term) :=
  parens ("program" ++ " " ++ "1.1.0" ++ " " ++
    (pretty_print' t)
  )
.

(* λ(x : Int) . x *)
Definition identity_ast : term :=
  LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x")
.

(* (λ(x : Int) . (λ(y : Int). x + y)) 1 *)
Definition plus_ast : term :=
  (App
    (LamAbs "x" (Ty_Builtin DefaultUniInteger)
      (LamAbs "y" (Ty_Builtin DefaultUniInteger)
        (App (App (Builtin AddInteger) (Var "x")) (Var "y"))))
  (Constant (Ty_Builtin DefaultUniInteger) "1")).

(* Eval cbv in (print_as_program identity_ast). *)
