From MetaCoq.Utils Require Import utils.

From Coq Require Import List Arith String.
Import ListNotations.

(* List lemmas *)
Lemma app_cons_comm : forall {A} (l1 l2 : list A) x,
  (l1 ++ x :: l2) = (l1 ++ [x] ++ l2).
Proof.
  induction l1; auto.
Qed.

Lemma in_not_in : forall {A} (l : list A) (x x' : A),
  In x l ->
  ~ In x' l ->
  x <> x'.
Proof.
  unfold not. intros.
  subst. contradiction.
Qed.

Lemma not_in_snoc : forall {A} (l : list A) x a,
  x <> a /\ ~ (In x l) ->
  ~ (In x (l ++ [a])).
Proof.
  intros A x a l [Hneq HnIn].
  unfold not. intros Hin. rewrite in_app_iff in Hin.
  destruct Hin.
  - contradiction.
  - simpl in H. destruct H.
    + symmetry in H. contradiction.
    + apply H.
Qed.

Lemma nth_error_not_snoc : forall {A} (l : list A) n x x',
  ~ In x l ->
  n < List.length l ->
  nth_error (l ++ [x]) n = Some x' ->
  x <> x'.
Proof.
  intros. rewrite nth_error_app1 in H1; [|assumption].
  apply nth_error_In in H1. 
  symmetry. apply (in_not_in l); assumption.
Qed.

Lemma nth_error_middle : forall {A} (Γ1 Γ2 : list A) x n v,
  List.length Γ1 = n ->
  nth_error (Γ1 ++ x :: Γ2) n = Some v ->
  x = v.
Proof.
  intros.
  rewrite <- H in H0. rewrite nth_error_app2, Nat.sub_diag in H0.
  simpl in H0. inversion H0. reflexivity. reflexivity.
Qed.

Lemma nth_error_outer : forall {A} (l : list A) x,
  nth_error (l ++ [x]) (List.length l) = Some x.
Proof.
  intros.
  rewrite nth_error_app2, Nat.sub_diag.
  auto. apply Nat.le_refl.
Qed.

Lemma nth_error_not_bound : forall {A} (l : list A) x x' n,
  List.length l <> n ->
  nth_error (l ++ [x]) n = Some x' ->
  n < List.length l.
Proof.
  intros.
  apply nth_error_Some_length in H0.
  rewrite length_app in H0. simpl in H0.
  lia.
Qed.
