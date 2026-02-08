From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure.Typed Require Import Utils ResultMonad.
From MetaCoq.Erasure.Typed Require Import Annotations.
From MetaCoq.Erasure.Typed Require Import TypeAnnotations.
From MetaCoq.Utils Require Import MCList MCString MCPrelude utils.

From VTL Require Import Env PIR Utils.

From Coq Require Import String BinInt List.

Import EAst ExAst.
Import BasicAst Kernames ListNotations.
Import MCMonadNotation.

Notation "'bs_to_s' s" := (bytestring.String.to_string s) (at level 200).
Notation "'s_to_bs' s" := (bytestring.String.of_string s) (at level 200).
Local Coercion bytestring.String.to_string : bytestring.String.t >-> string.

Definition remap_ty (kn : kername) (uni : PIR.DefaultUni) := 
  (kn_to_s kn, PIR.Ty_Builtin uni).

Definition remap_env : env PIR.ty :=
  [
    remap_ty <%% Z    %%> (PIR.DefaultUniInteger);
    remap_ty <%% unit %%> (PIR.DefaultUniUnit);
    remap_ty <%% bool %%> (PIR.DefaultUniBool)
  ].

Definition remap_fun (kn : kername) (df : PIR.DefaultFun) :=
  (kn, PIR.Builtin df).

Definition pir_ignore_default : list kername :=
  [<%% positive %%>;
   <%% Z %%>;
   <%% unit %%>;
   <%% bool %%>].

Opaque pir_ignore_default.

Section translate.

Context (TT : env PIR.ty).

Definition entry := kername * binderName * binding.

Definition get_binder_names (Σ' : list entry) : list string :=
  map (fun '(_, kn', _) => kn') Σ'.

Definition gen_fresh_name na Σ' Γ :=
  match na with
  | nAnon => gen_fresh "anon" (get_binder_names Σ' ++ Γ)
  | nNamed id => gen_fresh id (get_binder_names Σ' ++ Γ) 
  end.

Lemma gen_fresh_name_fresh : forall Σ' Γ na,
  ~ In (gen_fresh_name na Σ' Γ) Γ.
Admitted.
  
Definition translate_ty : box_type -> option PIR.ty :=
  fix go (ty : box_type) :=
  match ty with
  | TBox => Some (PIR.Ty_Builtin (PIR.DefaultUniUnit))
  | TArr a b => 
    a' <- go a ;;
    b' <- go b ;;
    Some (PIR.Ty_Fun a' b')
  | TInd ind => lookup TT (kn_to_s ind.(inductive_mind))
  | _ => None
  end.

(* Interface so it is easy to add qualified part or change casing later *)
Definition gen_fresh_binder_name (kn : kername) (bs : list string) :=
  gen_fresh (kn.2) bs.

Definition lookup_constant_body (env : ExAst.global_env) kn : option EAst.term :=
  cst <- lookup_constant env kn ;;
  cst_body cst.

Definition lookup_entry (Σ' : list entry) (nm : kername) : option entry :=
  find (fun '(kn, _, _) => eq_kername kn nm) Σ'.

Fixpoint translate_term
         (Σ' : list entry) (Γ : list string)
         (t : term) {struct t} : annots box_type t -> option PIR.term :=
  match t return annots box_type t -> option PIR.term with
  | tBox => fun b_ty => Some (PIR.Constant (ValueOf DefaultUniUnit tt)) (* temporary constant *)
  | tRel n => fun b_ty =>
    match nth_error Γ n with
    | Some id => Some (PIR.Var id)
    | None => None
    end
  | tLambda x b => fun '(ty, ann_b) =>
    match ty with
    | TArr br_ty _ =>
      let x' := gen_fresh_name x Σ' Γ in
      br_ty' <- translate_ty br_ty ;;
      b' <- translate_term Σ' (x' :: Γ) b ann_b ;;
      Some (LamAbs x' br_ty' b')
    | _ => None
    end
  | tLetIn x br b => fun '(ty, (ann_br, ann_b)) =>
    match ty with
    | TArr br_ty _ =>
      let x' := gen_fresh_name x Σ' Γ in
      br_ty' <- translate_ty br_ty ;; 
      br' <- translate_term Σ' Γ br ann_br ;;
      b' <- translate_term Σ' (x' :: Γ) b ann_b ;;
      Some (Let [TermBind (VarDecl x' br_ty') br'] b')
    | _ => None
    end
  | tApp f a => fun '(_, (ann_f, ann_a)) =>
    f' <- translate_term Σ' Γ f ann_f ;;
    a' <- translate_term Σ' Γ a ann_a ;;
    Some (Apply f' a')
  | tConst kn => fun bt =>
    match lookup_entry Σ' kn with
    | Some (_, kn', _)=> Some (Var kn')
    | None => None end
  | _ => fun _ => None
  end.

Definition translate_constant
           (Σ' : list entry)
           (cst : constant_body)
           (kn : kername)
           (ann_c : constant_body_annots box_type cst) : option entry.
Proof.
  destruct cst as [[params ty] body].
  destruct body as [t|]; [|exact None]. (* no axioms allowed *)
  destruct (translate_ty ty) as [ty'|]; [|exact None].
  destruct (translate_term Σ' [] t ann_c) as [t'|]; [|exact None].
  pose (kn' := gen_fresh_binder_name kn (map (fun '(_, nm, _) => nm) Σ')).
  exact (Some (kn, kn', TermBind (VarDecl kn' ty') t')).
Defined.

Local Open Scope string_scope.

Fixpoint translate_env (eΣ : global_env) : env_annots box_type eΣ -> result (list entry) string :=
  match eΣ return env_annots box_type eΣ -> result (list entry) string with
  | [] => fun _ => Ok []
  | ((kn, deps, decl) :: decls) => fun '(ann_d, anns) =>
    match translate_env decls anns with
    | Ok Σ' =>
      match decl, ann_d with
      | ConstantDecl cst, ann_c =>
        match translate_constant Σ' cst kn ann_c with
        | Some entry => Ok (entry :: Σ')
        | None => Err ("Failed to translate constant " ++ kn_to_s kn)
        end
      | InductiveDecl _, _ => (* we ignore certain inductives until the remapping of inductives has been implemented *)
        match find (fun nm => eq_kername kn nm) pir_ignore_default with
        | Some res => Ok Σ'
        | None => Err ("Inductive " ++ kn_to_s kn ++ " not found in translation table, 
                       true inductives are not supported yet") end
      | _, _ => Err ("Type aliases are not supported yet")
      end
    | Err e => Err e
    end
  end.

Definition bind_pir_env (Σ' : list entry) (body : PIR.term) : PIR.term :=
  Let (map (fun '(_, _, b) => b) (rev Σ')) body.

Definition get_entry_body (e : entry) : PIR.term :=
  match e with
  | (_, _, TermBind (VarDecl _ _) t') => t' 
  end.

Definition typed_eprogram := (∑ env : ExAst.global_env, env_annots box_type env) * kername.

Definition translate_typed_eprogram (epT : typed_eprogram) : result PIR.term string :=
  let '((eΣ; ann_env), init) := epT in
  match translate_env eΣ ann_env with
  | Ok Σ' =>
    match lookup_entry Σ' init with
    | Some (_, init', _) => Ok (bind_pir_env Σ' (Var init'))
    | None => Err ("Initial definition " ++ kn_to_s init ++ " not found in environment.") end
  | Err e => Err ("Failed to translate environment: " ++ e) end.

Inductive translatesTypeTo : box_type -> PIR.ty -> Prop :=
  | tlty_tt : translatesTypeTo TBox (PIR.Ty_Builtin DefaultUniUnit)
  | tlty_fun : forall ty1 ty2 ty1' ty2',
      translatesTypeTo ty1 ty1' ->
      translatesTypeTo ty2 ty2' ->
      translatesTypeTo (TArr ty1 ty2) (PIR.Ty_Fun ty1' ty2')
  | tlty_ind : forall ind ty',
      lookup TT (string_of_kername ind.(inductive_mind)) = Some ty' ->
      translatesTypeTo (TInd ind) ty'.

Inductive translatesTo (Σ' : list entry) (Γ : list string) : forall (t : term),
  annots box_type t -> PIR.term -> Prop :=
  | tlt_tt : forall ann, translatesTo Σ' Γ tBox ann (Constant (ValueOf DefaultUniUnit tt))
  | tlt_rel : forall n x ann,
      find_index_string Γ x = Some n ->
      translatesTo Σ' Γ (tRel n) ann (Var x)
  | tlt_lambda : forall x x' arg_ty res_ty b ann_b arg_ty' b',
      translatesTypeTo arg_ty arg_ty' ->
      translatesTo Σ' (x' :: Γ) b ann_b b' ->
      translatesTo Σ' Γ (tLambda x b) (TArr arg_ty res_ty, ann_b) (LamAbs x' arg_ty' b')
  | tlt_let : forall x x' br_ty b_ty br b ann_br ann_b br_ty' br' b',
      translatesTypeTo br_ty br_ty' ->
      translatesTo Σ' Γ br ann_br br' ->
      translatesTo Σ' (x' :: Γ) b ann_b b' ->
      translatesTo Σ' Γ (tLetIn x br b) (TArr br_ty b_ty, (ann_br, ann_b)) (Let [(TermBind (VarDecl x' br_ty') br')] b')
  | tlt_app : forall t1 t2 ann_t1 ann_t2 ty t1' t2',
      translatesTo Σ' Γ t1 ann_t1 t1' ->
      translatesTo Σ' Γ t2 ann_t2 t2' ->
      translatesTo Σ' Γ (tApp t1 t2) (ty, (ann_t1, ann_t2)) (PIR.Apply t1' t2')
  | tlt_const : forall kn kn' br ann,
      lookup_entry Σ' kn = Some (kn, kn', br) ->
      translatesTo Σ' Γ (tConst kn) ann (Var kn').

Definition translatesConstant (Σ' : list entry) 
           (cb : constant_body) (ann_cb : constant_body_annots box_type cb)
           (cb' : entry) : Prop.
Proof.
  destruct cb as [args cst_body].
  destruct cb' as [[e_kn e_kn'] [v t']].
  - destruct cst_body.
    + exact (translatesTo Σ' [] t ann_cb t').
    + exact False.
Defined.

Definition translatesDecl (Σ' : list entry) 
           (decl : global_decl) (ann_decl : global_decl_annots box_type decl)
           (entry : entry) : Prop.
Proof.
  destruct decl.
  - simpl in ann_decl.
    exact (translatesConstant Σ' c ann_decl entry).
  - exact False.
  - exact False.
Defined.

Inductive translatesEnv : forall (Σ : global_env) (Σ' : list entry), env_annots box_type Σ -> Prop :=
  | tlte_empty : forall ann_env, translatesEnv [] [] ann_env
  | tlte_const : forall Σ Σ' kn deps decl ann_decl entry (ann_env : env_annots box_type Σ),
      translatesDecl Σ' decl ann_decl entry ->
      translatesEnv (((kn, deps), decl) :: Σ) (entry :: Σ') (ann_decl, ann_env)
  | tlte_remap : forall Σ Σ' kn deps ind ann_ind ann_env,
      find (fun nm : kername => kn == nm) pir_ignore_default = Some kn ->
      translatesEnv Σ Σ' ann_env ->
      translatesEnv (((kn, deps), InductiveDecl ind) :: Σ) Σ' (ann_ind, ann_env).

Theorem translate_type_reflect : forall ty ty',
  translate_ty ty = Some ty' -> translatesTypeTo ty ty'.
Proof.
  intros ty ty'. revert ty'. induction ty; try discriminate; 
  intros ty' tl_ty; inversion tl_ty.
    + apply tlty_tt.
    + destruct (translate_ty ty1) as [ty1'|]; [|discriminate].
      destruct (translate_ty ty2) as [ty2'|]; [|discriminate].
      specialize (IHty1 ty1' eq_refl).
      specialize (IHty2 ty2' eq_refl).
      inversion H0 as [Hty'].
      now eapply tlty_fun.
    + now apply tlty_ind.
Qed.

Theorem translate_reflect : forall Σ' Γ t t' (ann : annots box_type t),
  NoDup Γ ->
  translate_term Σ' Γ t ann = Some t' -> translatesTo Σ' Γ t ann t'.
Proof.
  intros Σ' Γ t. revert Γ. induction t; try discriminate; 
  intros Γ t' ann nodup tl_t; inversion tl_t as [Ht].
  - apply tlt_tt.
  - destruct (nth_error Γ n) eqn:El; [|discriminate].
    inversion Ht as [Ht']. apply tlt_rel. 
    now apply nth_error_to_find_index in El. 
  - destruct ann as [[] ann_b]; try discriminate.
    destruct (translate_ty dom) as [br_ty'|] eqn:tl_ty; [|discriminate].
    destruct (translate_term Σ' (gen_fresh_name na Σ' Γ :: Γ) t ann_b) as [b'|] eqn:tl_b; 
    [|discriminate]. inversion Ht as [Ht']. set (na' := gen_fresh_name na Σ' Γ). 
    assert (nodup' : NoDup (na' :: Γ)).
    apply NoDup_cons; try assumption.
    apply gen_fresh_name_fresh.
    specialize (IHt (na' :: Γ) b' ann_b nodup' tl_b).
    apply (translate_type_reflect dom br_ty') in tl_ty.
    now apply tlt_lambda.
  - destruct ann as [[] [ann_br ann_b]]; try discriminate.
    destruct (translate_ty dom) as [br_ty'|] eqn:tl_ty; [|discriminate].
    destruct (translate_term Σ' Γ t1 ann_br) as [br'|] eqn:tl_br; [|discriminate].
    destruct (translate_term Σ' (gen_fresh_name na Σ' Γ :: Γ) t2 ann_b) as [b'|] eqn:tl_b; 
    [|discriminate]. inversion Ht as [Ht']. set (na' := gen_fresh_name na Σ' Γ).
    assert (nodup' : NoDup (na' :: Γ)).
    apply NoDup_cons; try assumption. 
    apply gen_fresh_name_fresh.
    specialize (IHt1 Γ br' ann_br nodup tl_br).
    specialize (IHt2 (na' :: Γ) b' ann_b nodup' tl_b).
    apply (translate_type_reflect dom br_ty') in tl_ty.
    now apply tlt_let.
  - destruct ann as [ty [ann_t1 ann_t2]].
    destruct (translate_term Σ' Γ t1 ann_t1) as [t1'|] eqn:tl_t1; [|discriminate].
    destruct (translate_term Σ' Γ t2 ann_t2) as [t2'|] eqn:tl_t2; [|discriminate].
    inversion Ht as [Ht'].
    specialize (IHt1 Γ t1' ann_t1 nodup tl_t1).
    specialize (IHt2 Γ t2' ann_t2 nodup tl_t2).
    now apply tlt_app.
  - destruct (lookup_entry Σ' k) as [[[kn kn'] br]|] eqn:El; [|discriminate].
    inversion Ht as [Ht']. apply find_some in El as Hl.
    destruct Hl as [Hin Heq]. apply ReflectEq.eqb_eq in Heq. subst.
    now eapply tlt_const.
Qed.

Theorem translate_env_reflect : forall Σ Σ' ann_env,
  translate_env Σ ann_env = Ok Σ' -> translatesEnv Σ Σ' ann_env.
Proof.
  intros Σ Σ' ann_env tl_env.
  induction Σ.
  - inversion tl_env. 
    apply tlte_empty.
  - destruct ann_env as [ann_decl ann_env'].
    destruct a as [[kn deps] decl].
    simpl in tl_env.
    destruct (translate_env Σ ann_env') as [Σ''|err] eqn:tl_env'; try discriminate.
    destruct decl.
    + destruct (translate_constant Σ'' c kn ann_decl) eqn:tl_constant; try discriminate.
      inversion tl_env. subst.
      econstructor. simpl. 
      destruct c as [[nm ty] [t|]]; try discriminate.
      { simpl in tl_constant.
        destruct (translate_ty ty) eqn:tl_ty; try discriminate.
        destruct (translate_term Σ'' [] t ann_decl) eqn:tl_t; try discriminate.
        apply translate_reflect in tl_t; [|apply NoDup_nil].
        destruct e as [[e_kn e_kn'] [v t']]. simpl.
        inversion tl_constant. subst t1.
        assumption. }
    + destruct (find (fun nm : kername => kn == nm) pir_ignore_default) eqn:Hremap; try discriminate.
      inversion tl_env. subst.
      apply find_some in Hremap as Heq. 
      destruct Heq as [_ Heq]. apply ReflectEq.eqb_eq in Heq. subst.
      constructor; auto.
    + discriminate.
Qed.

End translate.

Definition translate_unsafe Γ (t : term) (ann : annots box_type t) := 
  with_default (PIR.Error (PIR.UNDEFINED "TranslationFailed")) (translate_term remap_env [] Γ t ann).

(* Lambda Box T is the combination of an EAst term with a dependent tree of its types *)
Definition identity_EAst : term :=
  tLambda (nNamed "x") 
    (tRel 0).

Definition Z_ind := TInd (mkInd <%% Z %%> 0).
Definition ann_id :=
  (TArr Z_ind Z_ind, Z_ind).

Definition id_twice := tLambda (nNamed "y") (tApp (tConst <%% identity_EAst %%>) (tRel 0)).
Definition ann_twice := (TArr Z_ind Z_ind, (Z_ind, (TArr Z_ind Z_ind, Z_ind))).

Definition c_id : constant_body := Build_constant_body ([], ann_id.1) (Some identity_EAst).
Definition decl_id := (<%% identity_EAst %%>, false, Ex.ConstantDecl c_id).

Definition c_twice := Build_constant_body ([], ann_twice.1) (Some id_twice).
Definition decl_twice := (<%% id_twice %%>, false, Ex.ConstantDecl c_twice).

(* Eval cbv in (translate_unsafe [] identity_EAst ann_id). *)

Definition example : (∑ env, env_annots box_type env) := ([decl_twice; decl_id]; (ann_twice, (ann_id, tt))).
(* Eval vm_compute in translate_typed_eprogram remap_env (example, <%% id_twice %%>). *)
