From MetaCoq.Erasure.Typed Require Import Utils WcbvEvalAux.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Loader.
From VTL Require Import PIR BigStepPIR Translation.

Existing Instance EWcbvEval.default_wcbv_flags.
Locate string.
(* restrict to Z type *)
Definition gal_id :=
  tLambda (BasicAst.nNamed "x") (tVar "x").

(* Refine and solve proof *)
Lemma galEvalId : [] e⊢ gal_id ⇓ gal_id.
Proof.
  intros. eauto.
Qed.

Inductive gValue : EAst.term -> Prop :=
  | gV_Lambda : forall n t, 
      gValue (tLambda n t)
  | gV_Constant : forall v, 
      gValue (tConst v).

Import PlutusNotations.
From Coq Require Import String BinInt.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition pir_id := <{λ "x" :: ℤ, {Var "x"} }>.

(* Can this become even shorter using a hint database? *)
Lemma pirEvalInt : forall y, <{pir_id ⋅ CInt y}> ⇓ <{CInt y}>.
Proof with (eauto using eval).
  split. eexists. econstructor... simpl... constructor.
Qed.

Definition faif := <% 5 %>.
Print faif.
MetaCoq Erase faif.

Definition zInd := Kernames.mkInd <%% Z %%> 0.
Definition zZero := tConstruct zInd 0 [].
Definition zPos := tConstruct zInd 1 [].
Definition zNeg := tConstruct zInd 2 [].
Definition zFive := mkApp zPos zZero.
Print mkApp.

Print positive.
Fixpoint toZ (num : Z) :=
  match num with
  | Z0 => zZero
  | Zpos z' => mkApp zPos (toZ z')
  end
.

Print Kernames.inductive.
Eval cbv in zZero.
Check Kernames.mkInd <%% Z %%> 0.
Check tConstruct.
(* For now, any const is equal to each other *)
Inductive eqConst : Kernames.kername -> constant -> Prop :=
| Eq_ConstVal : forall kn cst, eqConst kn cst.

Eval cbv in <% 5 %>.
Eval cbv in <% <{ CInt 5 }> %>.
Lemma correct5 : 
  let gFive := <% 5 %> in
  let pFive := <{ CInt 5 }> in (translate_term remap_env gFive) tBox = pFive.

(* Define correspondence of values (how to add types?) *)
(* how to define alpha, beta, eta equivalence for lambda values *)
Inductive eqValues : EAst.term -> PIR.term -> Prop :=
  | Eq_Lambda : forall n t x T t0, (get_name n) = x ->
      eqValues (tLambda n t) (LamAbs x T t0)
  | Eq_Const : forall v1 v2, eqConst v1 v2 ->
      eqValues (tConst v1) (Constant v2).

Check ((translate_term remap_env gal_id) ann_id).

Theorem id_correct : [] e⊢ gal_id ⇓ gal_id ->
  ((translate_term remap_env gal_id) ann_id) ⇓ ((translate_term remap_env gal_id) ann_id).
Proof.
  intros.
  unfold gal_id in *.
  simpl in *. split.
  - eexists. eapply E_LamAbs. eauto.
  - constructor.
Qed.

Theorem translation_correct : 
  forall Σ (gt gv : EAst.term) (pt : PIR.term) pv ,
  Σ e⊢ gt ⇓ gv ->
  pt ⇓ pv ->
  ((translate_term remap_env gt) ann_id) = pt ->
  eqValues gv pv.
