From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Kernames Transform config.
From MetaCoq.Template Require Import Ast Loader TemplateMonad TemplateProgram.
From MetaCoq.Erasure Require Import ExAst EProgram EWellformed EWcbvEval.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations Erasure Utils.
From MetaCoq.Erasure.Typed Require Import Extraction ResultMonad Optimize.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.

From VTL Require Import PIR Utils.
From VTL Require Import Translation.

From Coq.Strings Require Import String.
Import MCMonadNotation ListNotations.

Local Existing Instance fake_guard_impl_instance.
Local Existing Instance extraction_checker_flags.

Definition gal_id := fun x : Z => x.

Import Common.Transform.Transform.

From VTL Require Import Pipeline Pretty.
Import Tree.

(* Definition print_constant_body_ann *)

(* Definition print_decl_ann '(kn, d) :=
  match d with
  | ConstantDecl c  => "Definition "  ^ string_of_kername kn (* expand *)
  | InductiveDecl _ => "INDUCTIVE " ^ string_of_kername kn
  | TypeAliasDecl _ => "TYPEALIAS " ^ string_of_kername kn
  end. *)

Definition print_constant_ann
           (eΣ : global_env)
           '((c; ann_c) : (∑ c : constant_body, constant_body_annots box_type c))
           kn :=
  match c, ann_c with
  | (Build_constant_body params (Some b)), ann_b =>
    "Definition " ^ string_of_kername kn (* params ^ *) ^ " : "
    ^ (s_to_bs print_box_type (annot ann_b)) ^ " := " 
    ^ nl ^ EPretty.pr (trans_env eΣ) b
  | _, _ => "Failed to translate constant " ^ string_of_kername kn
  end.

Definition print_def '((kn, (eΣ; ann_env)) : kername * (∑ eΣ : global_env, env_annots box_type eΣ)) :=
  match bigprod_find (fun '(k, _, _) _ => eq_kername k kn) ann_env with
  | Some (((kn, deps), ConstantDecl c); ann_c) => print_constant_ann eΣ (c; ann_c) kn
  | _ => "Failed to translate definition " ^ string_of_kername kn
  end.

Definition print_simplified_typed_eprogram (epT : typed_eprogram) :=
  let '((eΣ; ann_env), init) := epT in
  let env_string  := print_list print_def nl (map (fun '((kn, _), d) => (kn, (eΣ; ann_env))) eΣ) in
  Tree.to_string env_string ^ nl ^ nl ^ 
  "init: " ^ print_def (init, (eΣ; ann_env)).

Definition show_pipeline (p : Ast.Env.program) :=
  let epT := run gallina_to_lbt_transform p I in
  let p' := compile_pir p in
  "Gallina: " ^ nl ^ Pretty.print_program true 5 p ^ nl ^ nl ^
  "λ□T: " ^ nl ^ Tree.to_string (print_simplified_typed_eprogram epT) ^ nl ^ nl ^ 
  "PIR: " ^ nl ^ (s_to_bs print_as_program p').

Definition test (gal_id gal_id' : Z) := gal_id'.
Eval vm_compute in show_pipeline <# test #>.
