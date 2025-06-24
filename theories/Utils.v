From MetaCoq.Utils Require Import utils.

From Coq Require Import Arith String List Lia.
Import ListNotations.

(* List lemmas *)
Lemma app_cons_comm : forall {A} (l1 l2 : list A) x,
  (l1 ++ x :: l2) = (l1 ++ [x] ++ l2).
Proof.
  induction l1; auto.
Qed.

Lemma length_pred_middle : forall {A} (l1 l2 : list A) x n,
  length l1 < n ->
  n < length (l1 ++ x :: l2) ->
  pred n < length (l1 ++ l2).
Proof.
  intros.
  rewrite length_app in *. simpl in H0.
  lia.
Qed.

Lemma length_middle : forall {A} (l1 l2 : list A) x n,
  n < length l1 ->
  n < length (l1 ++ x :: l2) ->
  n < length (l1 ++ l2).
Proof.
  intros. destruct l1.
  - inversion H.
  - rewrite length_app in *. lia.
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
  n < length l ->
  nth_error (l ++ [x]) n = Some x' ->
  x <> x'.
Proof.
  intros. rewrite nth_error_app1 in H1; [|assumption].
  apply nth_error_In in H1. 
  symmetry. apply (in_not_in l); assumption.
Qed.

Lemma nth_error_middle : forall {A} (Γ1 Γ2 : list A) x n v,
  length Γ1 = n ->
  nth_error (Γ1 ++ x :: Γ2) n = Some v ->
  x = v.
Proof.
  intros.
  rewrite <- H in H0. rewrite nth_error_app2, Nat.sub_diag in H0.
  simpl in H0. inversion H0. reflexivity. reflexivity.
Qed.

Lemma nth_error_outer : forall {A} (l : list A) x,
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros.
  rewrite nth_error_app2, Nat.sub_diag.
  auto. apply Nat.le_refl.
Qed.

Lemma nth_error_not_bound : forall {A} (l : list A) x x' n,
  length l <> n ->
  nth_error (l ++ [x]) n = Some x' ->
  n < length l.
Proof.
  intros.
  apply nth_error_Some_length in H0.
  rewrite length_app in H0. simpl in H0.
  lia.
Qed.

Lemma nth_error_Some_value : forall {A} (l : list A) n,
  n < length l ->
  exists v, nth_error l n = Some v.
Proof.
  intros A l; induction l; intros n Hl.
  - inversion Hl.
  - destruct n.
    + simpl. eauto.
    + simpl in *. apply IHl. 
      apply PeanoNat.lt_S_n in Hl. apply Hl.
Qed.
  
