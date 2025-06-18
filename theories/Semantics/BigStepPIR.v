From VTL Require Import PIR.
Import PlutusNotations.

Require Import Arith.
Local Open Scope nat_scope.

Require Import Lists.List.
Import ListNotations.

Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import FunInd.

Function subst (x : string) (s : term) (t : term) {struct t} : term :=
  match t with
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
.

Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom plutus_term at level 20, x constr).

(** * Big-step operational semantics *)
Reserved Notation "t '=[' j ']=>' v"(at level 40).

Fixpoint closedUnder Γ t : bool :=
  match t with
  | Var x => existsb (fun v => v =? x) Γ
  | Apply t1 t2 => closedUnder Γ t1 && closedUnder Γ t2
  | LamAbs x T b => closedUnder (x :: Γ) b
  | Constant _ => true
  | Builtin _ => true
  | _ => false end.

Notation closed t := (closedUnder nil t).

Lemma subst_closed : forall Γ t,
    closedUnder Γ t = true ->
    forall x s,
      <{ [x := s] t }> = t.
Proof. Admitted.

Function fv (t : term) : list string :=
    match t with
     | Var n           => [n]
     | LamAbs n ty t   => remove string_dec n (fv t)
     | Apply s t       => fv s ++ fv t
     | Builtin f       => []
     | Constant v      => []
     | Error ty        => []
   end.

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
  (** Builtins: partial application *)

where "t '=[' j ']=>' v" := (eval t v j).

Inductive value : term -> Prop :=
  | V_LamAbs : forall x T t0,
      value (LamAbs x T t0)
  | V_Constant : forall u,
      value (Constant u).

Definition evaluatesTo t v : Prop := 
  (exists k, t =[k]=> v) /\ value v.
Notation "t '⇓' v" := (evaluatesTo t v) (at level 100).
