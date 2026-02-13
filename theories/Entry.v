From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Utils Require Import MCList MCString MCPrelude utils.

From VTL Require Import Env PIR Utils.

From Coq Require Import String BinInt List.

Import EAst ExAst.
Import BasicAst Kernames ListNotations.
Import MCMonadNotation.

Definition fresh_pair := kername * binderName. 
Definition fresh_map := list (kername * binderName).

Definition entry := kername * binding.

Definition to_fresh_pair entry : fresh_pair :=
  match entry with
  | (kn, TermBind (VarDecl kn' ty') b') => (kn, kn')
  end.

Definition to_fresh_map (Σ' : list entry) : fresh_map :=
  map to_fresh_pair Σ'.

Definition get_entry_body (e : entry) : PIR.term :=
  match e with
  | (_, TermBind (VarDecl _ _) t') => t' 
  end.

Definition get_entry_nm (e : entry) : binderName :=
  match e with
  | (_, TermBind (VarDecl nm _) _) => nm
  end.

Definition get_binder_names (frmap : fresh_map) : list string :=
  map snd frmap.

Definition lookup_entry (Σ' : list entry) (nm : kername) : option entry :=
  find (fun '(kn, _) => eq_kername kn nm) Σ'.

Definition lookup_fresh (Σ_fresh : list fresh_pair) (nm : kername) : option fresh_pair :=
  find (fun '(kn, _) => eq_kername kn nm) Σ_fresh.

Lemma lookup_entry_key : forall Σ' k k' bnd,
  lookup_entry Σ' k = Some (k', bnd) ->
  k = k'.
Proof.
  intros. induction Σ'.
  - inversion H.
  - inversion H. destruct a.
    destruct (k0 == k) eqn:Heq.
    + now apply ReflectEq.eqb_eq in Heq. 
    + inversion H. now rewrite Heq in H2.
Qed.

Lemma lookup_fresh_key : forall frmap k k' kn',
  lookup_fresh frmap k = Some (k', kn') ->
  k = k'.
Proof.
  intros. induction frmap.
  - inversion H.
  - inversion H. destruct a.
    destruct (k0 == k) eqn:Heq.
    + now apply ReflectEq.eqb_eq in Heq. 
    + inversion H. now rewrite Heq in H2.
Qed.

Lemma lookup_entry_to_lookup_fresh : forall Σ' kn kn' ty' b',
  lookup_entry Σ' kn = Some (kn, TermBind (VarDecl kn' ty') b') ->
  lookup_fresh (to_fresh_map Σ') kn = Some (kn, kn').
Proof.
  intros. induction Σ'.
  - inversion H.
  - destruct a as [a_kn [[a_kn' a_ty'] a_b']]. simpl in *.
    destruct (a_kn == kn) eqn:Heq.
    + now inversion H.
    + now apply IHΣ'.
Qed.

Lemma lookup_entry_Some : forall Σ' kn kn' ty' b', 
  lookup_entry Σ' kn = Some (kn, TermBind (VarDecl kn' ty') b') ->
  In kn' (map (snd ∘ to_fresh_pair) Σ').
Proof.
  intros. induction Σ'.
  - discriminate.
  - destruct a as [a_kn [[a_kn' a_ty'] a_b']]. 
    simpl. simpl in H.
    destruct (a_kn == kn) eqn:Heq; inversion H; subst.
    + now left.
    + apply IHΣ' in H1. now right.
Qed.

Lemma lookup_fresh_Some : forall frmap kn kn', 
  lookup_fresh frmap kn = Some (kn, kn') ->
  In kn' (get_binder_names frmap).
Proof.
  intros. induction frmap.
  - discriminate.
  - destruct a as [a_kn a_kn'].
    simpl. simpl in H. eauto.
    destruct (a_kn == kn) eqn:Heq; inversion H; subst.
    + now left.
    + apply IHfrmap in H1. now right.
Qed.
