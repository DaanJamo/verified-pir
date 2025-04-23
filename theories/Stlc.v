From Coq Require Import Strings.String List.
Import ListNotations.

From VTL Require Import PIR BigStepPIR Env.

Module STLC.

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

Definition context := env ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm.
  (* | tm_if    : tm -> tm -> tm -> tm. *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
(* Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity). *)
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  (* | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}> *)
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Notation "x '|->' v ';' m " := ((x, v) :: m)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := ((x, v) :: nil)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

Notation "'empty'" := nil (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Γ '⊢' t '∈' T }>"
            (at level 0, Γ custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Γ x T1,
      lookup Γ x = Some T1 ->
      <{Γ ⊢ x ∈ T1 }>
  | T_Abs : forall Γ x T1 T2 t1,
      <{ x |-> T2 ; Γ ⊢ t1 ∈ T1 }> ->
      <{ Γ ⊢ \x:T2, t1 ∈ T2 -> T1 }>
  | T_App : forall T1 T2 Γ t1 t2,
      <{ Γ ⊢ t1 ∈ T2 -> T1 }> ->
      <{ Γ ⊢ t2 ∈ T2 }> ->
      <{ Γ ⊢ t1 t2 ∈ T1 }>
  | T_True : forall Γ,
      <{ Γ ⊢ true ∈ Bool }>
  | T_False : forall Γ,
      <{ Γ ⊢ false ∈ Bool }>
  (* | T_If : forall t1 t2 t3 T1 Γ,
       <{ Γ ⊢ t1 ∈ Bool }> ->
       <{ Γ ⊢ t2 ∈ T1 }> ->
       <{ Γ ⊢ t3 ∈ T1 }> ->
       <{ Γ ⊢ if t1 then t2 else t3 ∈ T1 }> *)

where "<{ Γ '⊢' t '∈' T }>" := (has_type Γ t T) : stlc_scope.

Hint Constructors has_type : core.

Definition typable (t : tm) := exists T, <{nil ⊢ t ∈ T}>.

Reserved Notation "s '==>' t" (at level 90, left associativity).

Inductive eval : tm -> tm -> Prop :=
  | E_Val : forall v,
    value v ->
    eval v v
  | E_App : forall t1 t2 x T b v2 v,
    t1 ==> <{\x : T, b}> ->
    t2 ==> v2 ->
    <{[x := v2] b}> ==> v ->
    <{t1 t2}> ==> v
  (* | E_If_True : forall b t1 t2 v1,
      b ==> <{true}> ->
      t1 ==> v1 ->
      <{if b then t1 else t2}> ==> v1
  | E_If_False : forall b t1 t2 v2,
      b ==> <{false}> ->
      t2 ==> v2 ->
      <{if b then t1 else t2}> ==> v2 *)

where "s '==>' t" := (eval s t).

Hint Constructors eval : core.

Fixpoint get_type ty : PIR.ty :=
  match ty with
  | Ty_Bool => PIR.Ty_Builtin DefaultUniBool
  | Ty_Arrow ty1 ty2 => PIR.Ty_Fun (get_type ty1) (get_type ty2) end.

Fixpoint translate tm : term :=
  match tm with
  | tm_var x => Var x
  | tm_app tm1 tm2 => Apply (translate tm1) (translate tm2)
  | tm_abs x T b => let ty := get_type T in LamAbs x ty (translate b)
  | tm_true => (Constant (ValueOf DefaultUniBool true))
  | tm_false => (Constant (ValueOf DefaultUniBool false))
  (* | tm_if tm1 tm2 tm3 => Apply (Builtin IfThenElse) t1 *) end.

Notation k := <{ \x:Bool, \y:Bool, x }>.

Eval cbv in (translate k).

Ltac solve_pir_eval := split; [(eexists ; eauto using BigStepPIR.eval) | constructor].

Theorem translate_id_correct : forall v,
  eval v v ->
  value v ->
  evaluatesTo (translate v) (translate v).
Proof.
  intros v ev vv. induction vv; solve_pir_eval.
Qed.

Lemma subst_same : forall x v b,
  translate <{ [x := v] b }> = BigStepPIR.subst x (translate v) (translate b).
Proof.
  intros x v b. induction b; simpl.
  - destruct (x =? s)%string; auto.
  - rewrite IHb1, IHb2. auto.
  - destruct (x =? s)%string; auto.
    simpl. rewrite IHb. auto.
  - auto.
  - auto.
Qed.

Theorem translate_correct : forall t v,
  eval t v ->
  exists k, BigStepPIR.eval (translate t) (translate v) k.
Proof.
  intros t v ev. induction ev.
  - eexists. induction H; (eauto using BigStepPIR.eval).
  - simpl in *. destruct IHev1, IHev2, IHev3. eexists.
    eapply E_Apply with (j1 := x1) (j2 := x2) (j0 := x3). eauto.
    apply H. apply H0. rewrite <- subst_same. apply H1.
Qed.
