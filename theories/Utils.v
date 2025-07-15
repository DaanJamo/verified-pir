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

Lemma In_not_In : forall {A} (l : list A) (x y : A),
  In x l ->
  ~ In y l ->
  x <> y.
Proof.
  unfold not. intros.
  subst. contradiction.
Qed.

Lemma In_middle : forall {A} (l : list A) (x y : A),
  x <> y ->
  In x (y :: l ++ [y]) ->
  In x l.
Proof.
  intros.
  inversion H0.
  symmetry in H1. contradiction.
  rewrite in_app_iff in H1.
  inversion H1. apply H2. inversion H2.
  symmetry in H3. contradiction.
  inversion H3.
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

Lemma nth_error_not_snoc : forall {A} (l : list A) n x y,
  ~ In x l ->
  n < length l ->
  nth_error (l ++ [x]) n = Some y ->
  x <> y.
Proof.
  intros. rewrite nth_error_app1 in H1; [|assumption].
  apply nth_error_In in H1. 
  symmetry. apply (In_not_In l); assumption.
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

Lemma nth_error_not_bound : forall {A} (l : list A) x y n,
  length l <> n ->
  nth_error (l ++ [x]) n = Some y ->
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

Lemma find_index_first : forall l x,
  find_index (x :: l) x = Some 0.
Proof.
  intros. unfold find_index.
  simpl. now rewrite eqb_refl.
Qed.

Lemma find_index_Some_first : forall l x n,
  find_index (x :: l) x = Some n ->
  n = 0.
Proof.
  intros. rewrite find_index_first in H.
  now inversion H.
Qed.

Lemma find_index_first_index : forall l x y,
  find_index (x :: l) y = Some 0 ->
  x = y.
Proof.
  intros.
  destruct_str_eq x y.
  + assumption.
  + unfold find_index in H. simpl in H. rewrite Heqb in H. 
    now apply find_index'_n_min_acc in H.
Qed. 

Lemma find_index_Some_single : forall x y n,
  find_index [x] y = Some n ->
  x = y.
Proof.
  intros x y n. unfold find_index. simpl.
  destruct (eqb x y) eqn:Heq.
  + now apply eqb_eq in Heq.
  + discriminate.
Qed.

Lemma find_index_single_index : forall x,
  find_index [x] x = Some 0.
Proof.
  intros. unfold find_index.
  simpl. now rewrite eqb_refl.
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

Lemma find_index_cons_other : forall l a x n,
  a <> x ->
  find_index l x = Some n ->
  find_index (a :: l) x = Some (S n).
Proof.
  intros l a x n Hneq Hfi. unfold find_index. 
  apply eqb_neq in Hneq. simpl. rewrite Hneq.
  now apply find_index'_acc_succ in Hfi.
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

Lemma find_index_inj : forall l x y n,
  find_index l x = Some n ->
  find_index l y = Some n ->
  x = y.
Proof.
  induction l; intros.
  - unfold find_index in H. simpl in H.
    discriminate H.
  - destruct_str_eq a x.
    + subst. apply find_index_Some_first in H.
      subst. now eapply find_index_first_index.
    + unfold find_index in *. simpl in *.
      rewrite Heqb in H.
      destruct_str_eq a y.
      * inversion H0. subst.
        apply find_index'_n_min_acc in H. lia.
      * specialize (IHl x y (pred n)).
        apply find_index'_n_min_acc in H as Hl.
        apply IHl; apply find_index'_acc_succ;
        rewrite Nat.succ_pred_pos; assumption.
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

Lemma find_index_weaken : forall l1 l2 x n,
  find_index l1 x = Some n ->
  find_index (l1 ++ l2) x = Some n.
Proof.
  intros.
  apply find_index_In in H as Hin.
  now rewrite find_index_app1.
Qed.

Lemma find_index_outer : forall l x y,
  find_index (l ++ [x]) y = Some (length l) ->
  x = y.
Proof.
  unfold find_index. induction l; intros.
  - simpl in H. destruct (eqb x y) eqn:Heq.
    + now apply eqb_eq in Heq.
    + discriminate.
  - apply IHl. simpl in H.
    destruct (eqb a y).
    + discriminate.
    + now apply find_index'_acc_succ.
Qed.

Lemma find_index_outer_not_In : forall l x,
  find_index (l ++ [x]) x = Some (length l) ->
  ~ In x l.
Proof.
  unfold not. intros.
  rewrite find_index_app1 in H; [|assumption].
  apply find_index_Some_length in H as Hl.
  now apply Nat.lt_irrefl in Hl.
Qed.

Lemma find_index_not_In : forall l1 l2 x n,
  find_index (l1 ++ l2) x = Some n ->
  n >= length l1 ->
  ~ In x l1.
Proof.
  unfold not. intros.
  rewrite find_index_app1 in H; [|assumption].
  apply find_index_Some_length in H as Hl.
  lia.
Qed.

Lemma find_index_not_outer : forall l x y n,
  x <> y ->
  find_index (l ++ [x]) y = Some n ->
  In y l.
Proof.
  intros. apply find_index_In in H0.
  rewrite in_app_iff in H0. inversion H0.
  apply H1. simpl in H1. inversion H1.
  contradiction. destruct H2.
Qed.

Lemma find_index_outer_length : forall l x y n,
  ~ In y l ->
  find_index (l ++ [x]) y = Some n ->
  n = length l.
Proof.
  intros. unfold find_index in H0.
  apply find_index'_app2 in H0. rewrite Nat.add_0_l in H0.
  apply find_index'_n_min_acc in H0 as Hl_min.
  apply find_index'_Some_length in H0 as Hl_max.
  simpl in *. lia. assumption.
Qed.

Lemma find_index_shadowed_length : forall l x y n,
  In y l ->
  find_index (l ++ [x]) y = Some n ->
  (length l =? n) = false.
Proof.
  intros l x y n Hin Hfi.
  rewrite find_index_app1 in Hfi; auto.
  apply find_index_Some_length in Hfi as Hl.
  now apply Nat.lt_neq, Nat.neq_sym, Nat.eqb_neq in Hl.
Qed.
  
Lemma find_index_app_iff : forall l1 l2 x n,
  find_index (l1 ++ l2) x = Some n ->
  In x l1 \/ (~ In x l1 /\ In x l2).
Proof.
  intros l1 l2 x n H. 
  apply find_index_In in H as Hin. revert H. 
  unfold find_index. generalize 0 as acc. 
  induction l1; intros acc H.
  - now right.
  - destruct_str_eq a x.
    + left. now left.
    + simpl in H. rewrite Heqb in H.
      inversion Hin. contradiction.
      apply IHl1 in H; auto. inversion H.
      * left. now right.
      * destruct H1. right. split. 
        simpl. unfold not. intros.
        inversion H3; contradiction.
        apply H2.
Qed.
