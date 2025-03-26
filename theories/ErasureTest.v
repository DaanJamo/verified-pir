From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure.Typed Require Import Utils ExAst.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Template Require Import All.
From MetaCoq.ErasurePlugin Require Import Erasure Loader.

From VTL Require Import PIR Translation.
Import MCMonadNotation.

MetaCoq Test Quote 3.

(* Print erase_and_print_template_program.
Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

MetaCoq Quote Recursively Definition idq := ((fun x => x + x) 3).

Locate typed_erasure_pipeline.
Eval cbv in erase_and_print_template_program default_erasure_config [] idq. *)
(* Definition erase {A} (a : A) : TemplateMonad EAst.term :=
  aq <- tmQuoteRec a ;;
  s <- tmEval lazy (erase_and_print_template_program default_erasure_config [] aq) ;;
  tmMsg s ;; ret EAst.tBox.

Definition compile_program (p : program) : PIR.term :=
  let (env, t) := p in
  PIR.Constant (ValueOf DefaultUniInteger 3%Z). *)

Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program default_erasure_config [] p.

MetaCoq Quote Recursively Definition zero := 0.

Definition zerocst := Eval lazy in test zero.
Print zerocst.

Definition singleton_elim :=
  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

MetaCoq Run (tmEval lazy singleton_elim >>= tmQuoteRec >>=
  fun p => tmEval lazy (test p) >>= tmPrint). (* Optimized to remove match on Props *)

MetaCoq Erase singleton_elim.

(* Definition Extraction (p : program) : TemplateMonad string :=
  match p.2 with
  |  *)

Definition do_nothing (tm : Ast.term) : TemplateMonad PIR.term :=
  match tm with
  | tLambda bind na body => ret (PIR.Builtin AddInteger)
  | _ => tmFail "nope!" end.

MetaCoq Run (tmUnquote <% bool %>).
MetaCoq Run (t <- tmQuote (fun x => x) ;; tmPrint t).
