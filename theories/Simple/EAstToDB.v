From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Utils Require Import utils.
Import BasicAst Kernames MCMonadNotation.

From VTL Require Import DBToPIR.

From Coq Require Import String BinInt List.
Import ListNotations.

Local Open Scope string_scope.

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).
Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.

(* hallucinates simple types for tm, maybe add synth_type *)
Fixpoint translate_et (Γ : list bs) t : option tm :=
  match t with
  | tConstruct _ _ _ => Some tm_true
  | tRel k => match nth_error Γ k with
              | Some _ => Some (tm_rel k)
              | None => None end
  | tLambda (nNamed x) b => 
      b' <- translate_et (x :: Γ) b ;;
      Some (tm_abs x (Ty_Arrow Ty_Bool Ty_Bool) b')
  | tApp s t =>
      s' <- translate_et Γ s ;;
      t' <- translate_et Γ t ;;
      Some (tm_app s' t')
  | _ => None
  end.

Definition tru := (tLambda (nNamed "t"%bs) (tLambda (nNamed "f"%bs) (tRel 0))).
(* Eval cbv in translate_et [] tru. *)
