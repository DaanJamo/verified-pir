From Coq Require Import String.
From Coq Require Import List.

Import ListNotations.

Definition env (A : Type) := list (string * A).

(** Lookup by variable name *)
Fixpoint lookup {A} (ρ : env A) (key : string) : option A :=
  match ρ with
  | [] => None
  | (nm, a) :: ρ' =>
    if (eqb nm key)
    then Some a
    else lookup ρ' key
  end.

Notation "ρ # '(' k ')'" := (lookup ρ k) (at level 65).
Notation "ρ # [ k ~> v ]" := ((k,v) :: ρ) (at level 65).

Definition with_default {A : Type} (default : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => default
  end.
