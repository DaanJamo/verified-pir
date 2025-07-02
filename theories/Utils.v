From MetaCoq.Utils Require Import utils.

From Coq Require Import Arith String List Lia.
Import ListNotations.

Ltac destruct_str_eq x y :=
  let H := fresh "Heqb" in
  destruct (Strings.String.eqb x y) eqn:H;
  [ let Heq := fresh "Heq" in apply Strings.String.eqb_eq in H as Heq
  | let Hneq := fresh "Hneq" in apply Strings.String.eqb_neq in H as Hneq].

Ltac destruct_nat_eq x y :=
  let H := fresh "Heqb" in
  destruct (Nat.eqb x y) eqn:H;
  [ let Heq := fresh "Heq" in apply Nat.eqb_eq in H as Heq
  | let Hneq := fresh "Hneq" in apply Nat.eqb_neq in H as Hneq].

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

Lemma not_in_snoc : forall {A} (l : list A) x a,
  x <> a /\ ~ (In x l) <->
  ~ (In x (l ++ [a])).
Proof.
  intros. rewrite in_app_iff. split.
  - intros [Hneq Hnin]. unfold not. intros Hin. 
    destruct Hin. contradiction. inversion H.
    symmetry in H0. contradiction. inversion H0.
  - intros. simpl in H.
    apply Decidable.not_or in H as [Hneq Hin].
    apply Decidable.not_or in Hin as [Hneq' _].
    split; auto.
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

Fixpoint find_index' (Γ : list string) x acc : option nat :=
  match Γ with
  | [] => None
  | h :: tl => if eqb h x then Some acc else find_index' tl x (S acc)
  end.

Definition find_index x Γ := find_index' x Γ 0.

Lemma find_index'_acc_succ : forall l x acc n,
  find_index' l x acc = Some n <->
  find_index' l x (S acc) = Some (S n).
Proof. induction l; intros; simpl.
  - split; congruence.
  - destruct (eqb a x).
    + split; congruence.
    + apply IHl.
Qed.

Lemma find_index'_n_min_acc : forall l x acc n,
  find_index' l x acc = Some n ->
  n >= acc.
Proof.
  induction l; intros.
  - inversion H.
  - simpl in H. destruct (eqb a x).
    + inversion H. apply Nat.le_refl.
    + apply IHl in H. lia.
Qed.

Lemma find_index'_Some_length : forall l x acc n,
  find_index' l x acc = Some n ->
  n < acc + length l.
  intros l x. induction l; intros acc n Hfi.
  - discriminate.
  - simpl in *.
    destruct (eqb a x).
    + inversion Hfi. lia.
    + apply IHl in Hfi. lia.
Qed.

Lemma find_index_Some_length : forall l x n,
  find_index l x = Some n ->
  n < length l.
Proof.
  intros l x. unfold find_index.
  apply find_index'_Some_length.
Qed.

Lemma find_index_Some_single : forall x x' n,
  find_index [x] x' = Some n ->
  x = x'.
Proof.
  intros x x' n. unfold find_index. simpl.
  destruct (eqb x x') eqn:Heq.
  + now apply eqb_eq in Heq.
  + discriminate.
Qed.

Lemma find_index_cons_succ : forall l a x n,
  find_index (a :: l) x = Some (S n) ->
  find_index l x = Some n.
Proof.
  intros l. unfold find_index.
  induction l; intros h x n Hfi.
  - simpl in Hfi. destruct (eqb h x); discriminate.
  - simpl in *. destruct (eqb h x).
    + discriminate.
    + destruct (eqb a x).
      * inversion Hfi. reflexivity.
      * now apply find_index'_acc_succ in Hfi.
Qed.

Lemma find_index_In : forall l x n,
  find_index l x = Some n ->
  In x l.
Proof.
  intros l x. induction l; intros n Hfi.
  - discriminate.
  - apply find_index'_Some_length in Hfi as Hl.
    unfold find_index in *. simpl in Hfi. 
    destruct (eqb a x) eqn:Heq.
    + apply eqb_eq in Heq. now left.
    + right. apply (IHl (pred n)).
      apply find_index'_acc_succ.
      rewrite Nat.succ_pred. apply Hfi.
      apply find_index'_n_min_acc in Hfi.
      lia.
Qed.  
      
Lemma find_index_app1 : forall l1 l2 x,
  In x l1 ->
  find_index (l1 ++ l2) x = find_index l1 x.
Proof.
  intros l1 l2 x Hin. unfold find_index.
  generalize 0 as acc. induction l1; intros acc.
  + inversion Hin.
  + simpl in *. destruct_str_eq a x.
    * reflexivity.
    * inversion Hin. contradiction.
      now apply IHl1.
Qed.

Lemma find_index'_app2 : forall l1 l2 x acc n,
  ~ In x l1 ->
  find_index' (l1 ++ l2) x acc = Some n ->
  find_index' (l2) x (acc + length l1) = Some (n).
Proof.
  intros l1 l2 x. induction l1; intros.
  - now rewrite Nat.add_0_r.
  - simpl in *. apply Decidable.not_or in H as [Hax Hin].
    apply eqb_neq in Hax. rewrite Hax in H0.
    specialize (IHl1 (S acc) n Hin H0).
    now replace (acc + S (length l1)) with (S acc + length l1) by lia.
Qed.

Lemma find_index_app2 : forall l1 l2 x n,
  ~ In x l1 ->
  find_index (l1 ++ l2) x = Some n ->
  find_index (l2) x = Some (n - length l1).
Proof.
  intros l1 l2 x. unfold find_index.
  generalize 0 as acc. induction l1; intros acc n Hnin Hfi.
  - simpl in *. now rewrite Nat.sub_0_r.
  - apply not_in_cons in Hnin as [Hneq Hnin].
    simpl in *. assert (a <> x) by auto.
    apply eqb_neq in H. rewrite H in Hfi.
    apply IHl1 in Hfi. apply find_index'_acc_succ.
    apply find_index'_n_min_acc in Hfi as Hl.
    rewrite Hfi. f_equal. lia. apply Hnin.
Qed.

Lemma find_index_outer : forall l x x',
  find_index (l ++ [x]) x' = Some (length l) ->
  x = x'.
Proof.
  unfold find_index. induction l; intros.
  - simpl in H. destruct (eqb x x') eqn:Heq.
    + now apply eqb_eq in Heq.
    + discriminate.
  - apply IHl. simpl in H.
    destruct (eqb a x').
    + discriminate.
    + now apply find_index'_acc_succ.
Qed.

Lemma find_index_not_outer : forall l x x' n,
  x <> x' ->
  find_index (l ++ [x]) x' = Some n ->
  In x' l.
Proof.
  intros. apply find_index_In in H0.
  rewrite in_app_iff in H0. inversion H0.
  apply H1. simpl in H1. inversion H1.
  contradiction. destruct H2.
Qed.

Lemma find_index_outer_length : forall l x x' n,
  ~ In x' l ->
  find_index (l ++ [x]) x' = Some n ->
  n = length l.
Proof.
  intros. unfold find_index in H0.
  apply find_index'_app2 in H0. rewrite Nat.add_0_l in H0.
  apply find_index'_n_min_acc in H0 as Hl_min.
  apply find_index'_Some_length in H0 as Hl_max.
  simpl in *. lia. assumption.
Qed.
  