From VTL Require Import PIR.
Import PlutusNotations.

Require Import Arith.
Local Open Scope nat_scope.

Require Import Lists.List.
Import ListNotations.

Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import FunInd.

Definition bvb (b : binding) : list binderName :=
  match b with
  | TermBind (VarDecl x _) _ => [x]
  end.
Definition bvbs (bs : list binding) := List.concat (map bvb bs).

Section SubstBindings.
  Context {subst_b : string -> term -> binding -> binding}.

  Function subst_bnr' (x : string) (s : term) (bs : list binding) : list binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        if existsb (eqb x) (bvb b)
          then
            subst_b x s b :: bs'
          else
            subst_b x s b :: subst_bnr' x s bs'
    end.

End SubstBindings.

Function subst (x : string) (s : term) (t : term) {struct t} : term :=
  match t with
    | Let bs t0 =>
      Let (@subst_bnr' subst_b x s bs)
        (if existsb (eqb x) (bvbs bs)
          then t0
          else subst x s t0
        )
  | Var y =>
      if x =? y
        then s
        else Var y
  | LamAbs bx T t0 =>
      if x =? bx
        then LamAbs bx T t0
        else LamAbs bx T (subst x s t0)
  | Apply t1 t2 =>
      Apply (subst x s t1) (subst x s t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | Error T =>
      Error T
  end

with
  subst_b (x : string) (s : term) (b : binding) {struct b} : binding :=
  match b with
  | TermBind (VarDecl y T) tb =>
      TermBind (VarDecl y T) (subst x s tb)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom plutus_term at level 20, x constr).

(** * Big-step operational semantics *)
Reserved Notation "t '=[' j ']=>' v"(at level 40).
Reserved Notation "t '=[' j ']=>nr' v"(at level 40).

Inductive eval : term -> term -> nat -> Prop :=
  | E_LamAbs : forall j x T t,
      j = 0 ->
      LamAbs x T t =[j]=> LamAbs x T t
  | E_Apply : forall j t1 t2 x T t0 v2 v0 j1 j2 j0,
      j = j1 + j2 + 1 + j0 ->
      t1 =[j1]=> LamAbs x T t0 ->
      t2 =[j2]=> v2 ->
      (* ~ is_error v2 -> *)
      <{ [x := v2 ] t0 }> =[j0]=> v0 ->
      Apply t1 t2 =[j]=> v0
  | E_Constant : forall j a,
      j = 0 ->
      Constant a =[j]=> Constant a
  (* | E_Error : forall j T,
      j = 0 ->
      Error T =[j]=> Error T
  | E_Error_Apply1 : forall j t1 t2 j1 T,
      j = j1 + 1 ->
      t1 =[j1]=> Error T ->
      Apply t1 t2 =[j]=> Error T
  | E_Error_Apply2 : forall j t1 t2 j2 T,
      j = j2 + 1 ->
      t2 =[j2]=> Error T ->
      Apply t1 t2 =[j]=> Error T *)
  (** let (non-recursive)*)
  | E_Let : forall bs t v j,
      Let bs t =[j]=>nr v ->
      Let bs t =[j]=> v

with eval_bindings_nonrec : term -> term -> nat -> Prop :=
  | E_Let_Nil : forall j t0 v0 j0,
      j = j0 + 1 ->
      t0 =[j0]=> v0 ->
      Let nil t0 =[ j ]=>nr v0
  | E_Let_TermBind_Strict : forall j x T t1 j1 v1 j2 v2 bs t0,
      j = j1 + 1 + j2 ->
      t1 =[j1]=> v1 ->
      (* ~ is_error v1 -> *)
      <{ [x := v1] {Let bs t0} }> =[j2]=>nr v2 ->
      Let ((TermBind (VarDecl x T) t1) :: bs) t0 =[j]=>nr v2

where "t '=[' j ']=>' v" := (eval t v j)
and "t '=[' j ']=>nr' v" := (eval_bindings_nonrec t v j).

Inductive value : term -> Prop :=
  | V_LamAbs : forall x T t0,
      value (LamAbs x T t0)
  | V_Constant : forall u,
      value (Constant u).

Definition evaluatesTo t v : Prop := 
  (exists k, t =[k]=> v) /\ value v.
Notation "t '⇓' v" := (evaluatesTo t v) (at level 100).
