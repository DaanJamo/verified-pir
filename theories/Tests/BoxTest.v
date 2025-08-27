From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast.
(* From MetaCoq.Template Require Import Loader. *)
From MetaCoq.TemplatePCUIC Require Import Loader.
From MetaCoq.ErasurePlugin Require Import Erasure.
From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Erasure.Typed Require Import Annotations TypeAnnotations.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import Extraction.
From Coq Require Import ZArith.
From Coq Require Import List.

Import MCMonadNotation.
Import ListNotations.

Program Definition cic_to_box p :=
  run_erase_program default_erasure_config ([], p) _.
Next Obligation.
  split. easy.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition no_check_args :=
  {| check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := false;
          extract_transforms := [dearg_transform (fun _ => None) false false false false false] |} |}.

Definition cic_to_box_typed p :=
  entry <- match p.2 with
           | tConst kn _ => Ok kn
           | tInd ind _ => Ok (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         no_check_args
         p.1
         (KernameSet.singleton entry)
         (fun _ => false);;
  Ok Σ.

(* Program Definition erase_type_of_program (p : Ast.Env.program) : P.global_env_ext * box_type :=
    let Σ := TemplateToPCUIC.trans_global_env p.1 in
    let Σext := P.empty_ext (PCUICProgram.trans_env_env Σ) in
    (Σext, erase_type_of Σext _ [] (Vector.nil _) (TemplateToPCUIC.trans Σ p.2) _).
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  MetaCoq Quote Recursively Definition eid := (fun (x : nat) => x).
  Eval cbv in (erase_type_of_program eid). *)

Definition eid := (fun (x : nat) => x).
(* MetaCoq Quote Recursively Definition t := eid. *)
Definition t := <# eid #>.
Eval cbv in (t.1).

Definition kn_eid : kername := (MPfile ["BoxTest"; "VTL"], "eid").
Definition Σ_eid := t.1.

Definition kns :=
  KernameSet.union (KernameSet.singleton kn_eid) (KernameSet.singleton (MPfile ["Datatypes"; "Init"; "Coq"], "nat")).

Definition pcuic_params :=
    {|
      optimize_prop_discr := true;
      extract_transforms :=
        [dearg_transform (fun _ : kername => None) true true true true true]
    |}
.

Definition eid_global_env_pcuic : PCUICAst.PCUICEnvironment.global_env
  := Σ_eid.1.(MetaCoq.PCUIC.PCUICProgram.trans_env_env).

Eval cbv in
  check_wf_env_func
    extract_within_coq
    eid_global_env_pcuic
    .

Definition Σ_wf := assume_env_wellformed eid_global_env_pcuic.

Eval vm_compute in
  extract_pcuic_env
    pcuic_params
    eid_global_env_pcuic
    Σ_wf
    (KernameSet.singleton kn_eid)
    (fun _ => true).


Definition nat_quoted :=
                  PCUICAst.PCUICEnvironment.InductiveDecl
                    {|
                      ExtractionCorrectness.PEnv.ind_finite := Finite;
                      ExtractionCorrectness.PEnv.ind_npars := 0;
                      ExtractionCorrectness.PEnv.ind_params := [];
                      ExtractionCorrectness.PEnv.ind_bodies :=
                        [{|
                           ExtractionCorrectness.PEnv.ind_name := "nat";
                           ExtractionCorrectness.PEnv.ind_indices := [];
                           ExtractionCorrectness.PEnv.ind_sort :=
                             sType
                               {|
                                 t_set :=
                                   {|
                                     LevelExprSet.this := [(Level.lzero, 0)];
                                     LevelExprSet.is_ok :=
                                       LevelExprSet.Raw.singleton_ok
                                         (Level.lzero, 0)
                                   |};
                                 t_ne := eq_refl
                               |};
                           ExtractionCorrectness.PEnv.ind_type :=
                             PCUICAst.tSort
                               (sType
                                  {|
                                    t_set :=
                                      {|
                                        LevelExprSet.this :=
                                          [(Level.lzero, 0)];
                                        LevelExprSet.is_ok :=
                                          LevelExprSet.Raw.singleton_ok
                                            (Level.lzero, 0)
                                      |};
                                    t_ne := eq_refl
                                  |});
                           ExtractionCorrectness.PEnv.ind_kelim := IntoAny;
                           ExtractionCorrectness.PEnv.ind_ctors :=
                             [{|
                                ExtractionCorrectness.PEnv.cstr_name := "O";
                                ExtractionCorrectness.PEnv.cstr_args := [];
                                ExtractionCorrectness.PEnv.cstr_indices := [];
                                ExtractionCorrectness.PEnv.cstr_type :=
                                  PCUICAst.tRel 0;
                                ExtractionCorrectness.PEnv.cstr_arity := 0
                              |};
                              {|
                                ExtractionCorrectness.PEnv.cstr_name := "S";
                                ExtractionCorrectness.PEnv.cstr_args :=
                                  [{|
                                     decl_name :=
                                       {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant
                                       |};
                                     decl_body := None;
                                     decl_type := PCUICAst.tRel 0
                                   |}];
                                ExtractionCorrectness.PEnv.cstr_indices := [];
                                ExtractionCorrectness.PEnv.cstr_type :=
                                  PCUICAst.tProd
                                    {|
                                      binder_name := nAnon;
                                      binder_relevance := Relevant
                                    |} (PCUICAst.tRel 0)
                                    (PCUICAst.tRel 1);
                                ExtractionCorrectness.PEnv.cstr_arity := 1
                              |}];
                           ExtractionCorrectness.PEnv.ind_projs := [];
                           ExtractionCorrectness.PEnv.ind_relevance :=
                             Relevant
                         |}];
                      ExtractionCorrectness.PEnv.ind_universes :=
                        Monomorphic_ctx;
                      ExtractionCorrectness.PEnv.ind_variance := None
                    |}
                    .

Require Import Strings.String.
Open Scope string_scope.



(* TODO: DEBUGGING erase_global_decl on nat global decl *)

Definition nat_kn :=
  (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs).

Definition nat_global_decl :=
             InductiveDecl
               {|
                 TemplateToPCUICCorrectness.S.Env.ind_finite := Finite;
                 TemplateToPCUICCorrectness.S.Env.ind_npars := 0;
                 TemplateToPCUICCorrectness.S.Env.ind_params := [];
                 TemplateToPCUICCorrectness.S.Env.ind_bodies :=
                   [{|
                      TemplateToPCUICCorrectness.S.Env.ind_name := "nat"%bs;
                      TemplateToPCUICCorrectness.S.Env.ind_indices := [];
                      TemplateToPCUICCorrectness.S.Env.ind_sort :=
                        sType
                          {|
                            t_set :=
                              {|
                                LevelExprSet.this := [(Level.lzero, 0)];
                                LevelExprSet.is_ok :=
                                  LevelExprSet.Raw.singleton_ok
                                    (Level.lzero, 0)
                              |};
                            t_ne := eq_refl
                          |};
                      TemplateToPCUICCorrectness.S.Env.ind_type :=
                        tSort
                          (sType
                             {|
                               t_set :=
                                 {|
                                   LevelExprSet.this := [(Level.lzero, 0)];
                                   LevelExprSet.is_ok :=
                                     LevelExprSet.Raw.singleton_ok
                                       (Level.lzero, 0)
                                 |};
                               t_ne := eq_refl
                             |});
                      TemplateToPCUICCorrectness.S.Env.ind_kelim := IntoAny;
                      TemplateToPCUICCorrectness.S.Env.ind_ctors :=
                        [{|
                           TemplateToPCUICCorrectness.S.Env.cstr_name :=
                             "O"%bs;
                           TemplateToPCUICCorrectness.S.Env.cstr_args := [];
                           TemplateToPCUICCorrectness.S.Env.cstr_indices :=
                             [];
                           TemplateToPCUICCorrectness.S.Env.cstr_type :=
                             tRel 0;
                           TemplateToPCUICCorrectness.S.Env.cstr_arity := 0
                         |};
                         {|
                           TemplateToPCUICCorrectness.S.Env.cstr_name :=
                             "S"%bs;
                           TemplateToPCUICCorrectness.S.Env.cstr_args :=
                             [{|
                                decl_name :=
                                  {|
                                    binder_name := nAnon;
                                    binder_relevance := Relevant
                                  |};
                                decl_body := None;
                                decl_type := tRel 0
                              |}];
                           TemplateToPCUICCorrectness.S.Env.cstr_indices :=
                             [];
                           TemplateToPCUICCorrectness.S.Env.cstr_type :=
                             tProd
                               {|
                                 binder_name := nAnon;
                                 binder_relevance := Relevant
                               |} (tRel 0) (tRel 1);
                           TemplateToPCUICCorrectness.S.Env.cstr_arity := 1
                         |}];
                      TemplateToPCUICCorrectness.S.Env.ind_projs := [];
                      TemplateToPCUICCorrectness.S.Env.ind_relevance :=
                        Relevant
                    |}];
                 TemplateToPCUICCorrectness.S.Env.ind_universes :=
                   Monomorphic_ctx;
                 TemplateToPCUICCorrectness.S.Env.ind_variance := None
               |}
.

Definition nat_env_ext := t.1.



Definition get_pair_of_first_constant (env : result ExAst.global_env string) :=
  match env with
  | Ok decls =>
      match decls with
      | (((kn, deps), decl) :: _) =>
          match decl with
          | ExAst.ConstantDecl cst =>
            match cst.(ExAst.cst_body) with
            | Some t => Ok (cst.(ExAst.cst_type).2, t)
            | None => Err "constant doesn't have a body" end
          | _ => Err "not a constant" end
      | _ => Err "empty environment" end
  | _ => Err "translation failed" end.

(* Example term *)
Definition t := fun (x : nat) => x.

(* Translate Coq def -> lambda_cic/Template program *)
MetaCoq Quote Recursively Definition ex1 := t.

(* Translate lambda_cic -> lambda_box *)
Eval vm_compute in cic_to_box ex1.

(* Translate lambda_cic -> lambda_boxtyped *)
(* Note that this only translates the environment *)
(* result ExAst.globalEnv string *)
(* ExAst.globalEnv = list ((kername x bool {has_deps}) x ExAst.global_decl)*)
Eval vm_compute in cic_to_box_typed ex1.
