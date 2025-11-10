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

Hint Constructors eval : core.
Hint Constructors eval_bindings_nonrec : core.

Inductive value : term -> Prop :=
  | V_LamAbs : forall x T t0,
    value (LamAbs x T t0)
  | V_Constant : forall u,
    value (Constant u).

Definition evaluatesTo t v : Prop := 
  (exists k, t =[k]=> v) /\ value v.
Notation "t '⇓ₚ' v" := (evaluatesTo t v) (at level 100).

From MetaCoq.Utils Require Import monad_utils.
From Coq Require Import Lia.
From VTL Require Import Env.

Import MCMonadNotation.

Fixpoint evaluate (t : term) (fuel : nat) : option term :=
  match fuel with
  | O => None
  | S fuel' =>
    match t with
    | Let [] t0 =>
      evaluate t0 fuel'
    | Let ((TermBind (VarDecl x T) t1) :: bs) t0 =>
      v1 <- evaluate t1 fuel';;
      evaluate <{ [x := v1] {Let bs t0} }> fuel'
    | Var x => None
    | LamAbs x T t0 => Some t
    | Apply f a =>
      match evaluate f fuel' with
      | Some (LamAbs x T t0) =>
        v <- evaluate a fuel';;
        evaluate (subst x v t0) fuel'
      | _ => None end
    | Constant u => Some t
    | _ => None
    end
  end.

Definition eval_pir (t : term) := evaluate t 1000.

From VTL Require Import Pretty.

Definition eval_pir_unsafe (t : term) :=
  match eval_pir t with
  | Some t' => t'
  | None => Error (UNDEFINED ("Evaluation of (" ++ show_term t ++ ") has failed."))
  end.

Definition eval_and_print_pir (t : term) := 
  print_as_program (eval_pir_unsafe t).

(* Eval vm_compute in eval_pir (Let [(TermBind (VarDecl "gal_id" <{ℤ}>) <{λ "x" :: ℤ, {Var "x"} }>)] (<{ {Var "gal_id"} ⋅ true }>)). *)

Lemma eval_subst : forall x v2 t v fuel,
  evaluate <{ [x := v2] t}> fuel = Some v ->
  exists j, fuel >= j -> eval <{ [x := v2] t}> v j.
Proof.
  intros x v2 t. induction t; intros v fuel Heval;
  destruct fuel; try discriminate; simpl in Heval.
  - destruct l.
    + simpl in *.
      apply IHt in Heval as [j H].
      eexists. constructor. econstructor.
      eauto. now apply H.
    + admit.
  - simpl in *. destruct (x =? n).
    + admit.
    + discriminate.
  - simpl. destruct (x =? b) eqn:Heq;
    now inversion Heval.
  - destruct (evaluate <{ [x := v2] t1 }> fuel) eqn:Hev1.
    destruct (evaluate <{ [x := v2] t2 }> fuel) eqn:Hev2.
    destruct t; try discriminate.
    destruct (IHt1 (LamAbs b t t3) fuel Hev1) as [j1 Hsub1].
    destruct (IHt2 t0 fuel Hev2) as [j2 Hsub2].
    eexists. intros. simpl. 
    econstructor. eauto. 
    apply Hsub1. lia.
    apply Hsub2. lia.
    admit. destruct t; discriminate. inversion Heval.
  - inversion Heval. simpl. eexists. eauto.
Admitted.

Lemma eval_reflect : forall t v fuel,
  evaluate t fuel = Some v ->
  exists j, fuel >= j -> eval t v j.
Proof.
  intros t. induction t; intros v fuel Heval;
  destruct fuel; try discriminate; simpl in Heval.
  - induction l.
    + apply IHt in Heval as [j Heval].
      exists (S j). intros. assert (fuel >= j) by lia.
      apply Heval in H0.
      constructor. econstructor. rewrite Nat.add_1_r. auto.
      apply H0.
    + eexists. intros.
      destruct a, v0; try discriminate.
      constructor. econstructor. eauto.
      * admit.
      * admit.
  - inversion Heval. eauto.
  - destruct (evaluate t1 fuel) eqn:Hev1; [|discriminate].
    destruct t; try discriminate.
    destruct (evaluate t2 fuel) eqn:Hev2; [|discriminate].
    apply IHt1 in Hev1. destruct Hev1 as [j1 Hev1].
    apply IHt2 in Hev2. destruct Hev2 as [j2 Hev2].
    apply eval_subst in Heval as [j3 Hev3].
    exists (j1 + j2 + 1 + j3). econstructor. eauto.
    apply Hev1. lia.
    apply Hev2. lia.
    apply Hev3. lia.
  - now inversion Heval.
Admitted.
