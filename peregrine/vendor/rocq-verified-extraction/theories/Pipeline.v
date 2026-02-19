(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICReduction PCUICAstUtils PCUICSN
    PCUICTyping PCUICProgram PCUICFirstorder PCUICEtaExpand.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EImplementBox EPretty Extract.
From MetaRocq Require Import ETransform EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EWcbvEvalNamed.
From MetaRocq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From Malfunction Require Import CompileCorrect SemanticsSpec FFI.
From Ceres Require Import CeresSerialize.
Import PCUICProgram.
(* Import TemplateProgram (template_eta_expand).
 *)
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Lemma All_sq {A} (P : A -> Type) l :
  Forall (fun x => squash (P x)) l ->
  squash (All P l).
Proof using Type.
  induction 1.
  - repeat econstructor.
  - sq. now constructor.
Qed.

Import Transform.Transform.

#[local] Arguments transform : simpl never.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

#[local] Existing Instance extraction_normalizing.

Import EWcbvEval.

From Malfunction Require Import Compile Serialize.

Record malfunction_pipeline_config :=
  { erasure_config :> erasure_configuration;
    reorder_cstrs : EProgram.inductives_mapping;
    prims : Malfunction.primitives }.

Definition int_to_nat (i : Uint63.int) : nat :=
  Z.to_nat (Uint63.to_Z i).

Definition array_length := Eval cbv in PArray.max_length.

Record good_for_extraction (fl : EWellformed.EEnvFlags) (p : program (list (kername × EAst.global_decl)) EAst.term) :=
  {
    few_enough_blocks :
      forall (i : inductive) (args : list nat), lookup_constructor_args p.1 i = Some args -> blocks_until #|args| args < 200 ;
    few_enough_constructors :
    forall (i : inductive) (mb : EAst.mutual_inductive_body)
      (ob : EAst.one_inductive_body),
      EGlobalEnv.lookup_inductive p.1 i = Some (mb, ob) ->
      #|EAst.ind_ctors ob| < Z.to_nat Malfunction.Int63.wB ;
    few_enough_arguments_in_constructors :
    forall (i : inductive) (mb : EAst.mutual_inductive_body)
      (ob : EAst.one_inductive_body),
      EGlobalEnv.lookup_inductive p.1 i = Some (mb, ob) ->
                             (forall (n : nat) (b : EAst.constructor_body),
                                 nth_error (EAst.ind_ctors ob) n = Some b ->
                                 EAst.cstr_nargs b < int_to_nat array_length) ;
    right_flags_in_glob : @EWellformed.wf_glob fl p.1 ;
    right_flags_in_term : @EWellformed.wellformed fl p.1 0 p.2
  }.

Notation "a &|& b" := (a && b) (at level 70).

Definition ignore {X Y} (x : X) (y : Y) := y.

Definition bool_good_error a s :=
  match a with
  | true => true
  | false => let r := coq_user_error s in ignore r false
  end.

Notation "a >>> s" := (bool_good_error a s) (at level 65).

Definition array_length_Z := Uint63.to_Z array_length.

From MetaRocq Require EWellformed.

Section params.

  Import EWellformed.

  Variables (efl : EWellformed.EEnvFlags) (Σ : EAst.global_declarations).

  Fixpoint wellformed_fast (t : EAst.term) {struct t} : bool :=
    match t with
    | EAst.tBox => EWellformed.has_tBox
    | EAst.tRel i => EWellformed.has_tRel
    | EAst.tVar _ => EWellformed.has_tVar
    | EAst.tEvar _ args => EWellformed.has_tEvar && forallb (wellformed_fast) args
    | EAst.tLambda _ M => EWellformed.has_tLambda && wellformed_fast M
    | EAst.tLetIn _ b b' => EWellformed.has_tLetIn && wellformed_fast b && wellformed_fast b'
    | EAst.tApp u v => EWellformed.has_tApp && wellformed_fast u && wellformed_fast v
    | EAst.tConst kn =>
        EWellformed.has_tConst
    | EAst.tConstruct ind c block_args =>
        EWellformed.has_tConstruct
    | EAst.tCase ind c brs =>
        EWellformed.has_tCase &&
          (let brs' := forallb (fun br : list BasicAst.name × EAst.term => wellformed_fast  br.2) brs in
           isSome (EGlobalEnv.lookup_inductive Σ ind.1) && wellformed_fast c && brs')
    | EAst.tProj p c => EWellformed.has_tProj && isSome (EGlobalEnv.lookup_projection Σ p) && wellformed_fast c
    | EAst.tFix mfix idx => EWellformed.has_tFix && forallb (EAst.isLambda ∘ EAst.dbody) mfix && EWellformed.wf_fix_gen (fun _ => wellformed_fast) 0 mfix idx
    | EAst.tCoFix mfix idx => EWellformed.has_tCoFix && EWellformed.wf_fix_gen (fun _ => wellformed_fast) 0 mfix idx
    | EAst.tPrim p => EWellformed.has_prim p && EPrimitive.test_prim (wellformed_fast) p
    | EAst.tLazy t0 | EAst.tForce t0 => EWellformed.has_tLazy_Force && wellformed_fast t0
    end.

End params.

Fixpoint check_good_for_extraction_rec (fl : EWellformed.EEnvFlags) (Σ : (list (kername × EAst.global_decl))) :=
  match Σ with
  | nil => true
  | (kn, EAst.ConstantDecl d) :: Σ =>
      match (EAst.cst_body d) with
      | Some b => if wellformed_fast fl Σ b
                  then check_good_for_extraction_rec fl Σ
                  else ignore (coq_msg_info "Warning: environment contains constructors for which extraction is not verified") (check_good_for_extraction_rec fl Σ)
      | None => ignore (coq_msg_info ("Warning: environment contains axiom " ++ Kernames.string_of_kername kn)) false
      end
  | (kn, EAst.InductiveDecl mind) :: Σ =>
      forallb (fun ob => let args := map EAst.cstr_nargs (EAst.ind_ctors ob) in
                 blocks_until #|args| args <? 200)  mind.(EAst.ind_bodies) >>> ("Inductive " ++ Kernames.string_of_kername kn ++ "has too many non-constant constructors, maximum 200 allowed")
      &|&
      forallb (fun ob => Z.of_nat #|EAst.ind_ctors ob| <? Malfunction.Int63.wB)%Z mind.(EAst.ind_bodies) >>> "inductive with too many constructors"
      &|&
      forallb (fun ob => forallb (fun b => Z.of_nat (EAst.cstr_nargs b) <? array_length_Z)%Z (EAst.ind_ctors ob)) mind.(EAst.ind_bodies) >>> "inductive with too many constructor arguments"
      &|& @EWellformed.wf_minductive fl mind >>> "environment contains non-extractable inductive"
      &|& check_good_for_extraction_rec fl Σ
  end.

Definition check_good_for_extraction fl (p : program (list (kername × EAst.global_decl)) EAst.term) :=
  if wellformed_fast fl p.1 p.2 then
    check_good_for_extraction_rec fl p.1
  else ignore (coq_msg_info "Warning: term contains constructors for which extraction is not verified") (check_good_for_extraction_rec fl p.1).

#[local] Obligation Tactic := try now program_simpl.

Definition extraction_term_flags_mlf :=
  {|
    EWellformed.has_tBox := true;
    EWellformed.has_tRel := true;
    EWellformed.has_tVar := false;
    EWellformed.has_tEvar := false;
    EWellformed.has_tLambda := true;
    EWellformed.has_tLetIn := true;
    EWellformed.has_tApp := true;
    EWellformed.has_tConst := true;
    EWellformed.has_tConstruct := true;
    EWellformed.has_tCase := true;
    EWellformed.has_tProj := false;
    EWellformed.has_tFix := true;
    EWellformed.has_tCoFix := false;
    EWellformed.has_tPrim :=
      {| EWellformed.has_primint := true;
         EWellformed.has_primfloat := true;
         EWellformed.has_primstring := false;
         EWellformed.has_primarray := false |};
    EWellformed.has_tLazy_Force := false
  |}.

Definition extraction_env_flags_mlf :=
  {|
    EWellformed.has_axioms := false;
    EWellformed.has_cstr_params := false;
    EWellformed.term_switches := extraction_term_flags_mlf;
    EWellformed.cstr_as_blocks := true |}.

Definition named_extraction_env_flags_mlf :=
  switch_env_flags_to_named (EImplementBox.switch_off_box extraction_env_flags_mlf).

Axiom assume_can_be_extracted : forall erased_program, good_for_extraction extraction_env_flags_mlf erased_program.

Program Definition enforce_extraction_conditions `{Pointer} `{Heap} :
  t EAst.global_declarations EAst.global_declarations EAst.term EAst.term EAst.term
    EAst.term
    (EProgram.eval_eprogram block_wcbv_flags) (EProgram.eval_eprogram block_wcbv_flags) :=
  {|
    name := "Enforce the term is extractable" ;
    transform p _ :=
      let r := check_good_for_extraction extraction_env_flags_mlf p in
      ignore r p ;
    (* if check_good_for_extraction extraction_env_flags_mlf p then p else p ; *)
    pre p := True ;
    post p := good_for_extraction extraction_env_flags_mlf p ;
    obseq p1 _ p2 v1 v2 := p1 = p2 /\ v1 = v2
  |}.
Next Obligation.
  program_simpl. apply assume_can_be_extracted.
Qed.
Next Obligation.
  program_simpl. red. program_simpl.  exists v. auto.
Qed.

From MetaRocq.Erasure Require Import EImplementBox EWellformed EProgram.

Lemma implement_box_good_for_extraction
  (efl := extraction_env_flags_mlf : EEnvFlags) :
  forall (input : program EAst.global_declarations EAst.term),
    good_for_extraction efl input -> good_for_extraction (switch_off_box efl) (implement_box_program input).
Proof.
  intros input p.
  destruct input as [Σ t].
  split.
  + intros.
    unfold lookup_constructor_args in H.
    rewrite lookup_inductive_implement_box in H. now eapply few_enough_blocks.
  + intros.
    rewrite lookup_inductive_implement_box in H. now eapply few_enough_constructors.
  + intros. rewrite lookup_inductive_implement_box in H. now eapply few_enough_arguments_in_constructors.
  + cbn. refine (@implement_box_env_wf_glob _ Σ _ _ _). reflexivity. reflexivity. apply p.
  + apply transform_wellformed'. all: try reflexivity. apply p. apply p.
Qed.

Program Definition implement_box_transformation (efl := extraction_env_flags_mlf) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := good_for_extraction efl p ;
    post p := good_for_extraction (switch_off_box efl) p /\ wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.
Next Obligation.
  intros. cbn in *. split. 2: split.
  - now eapply implement_box_good_for_extraction.
  - eapply implement_box_env_wf_glob; eauto. apply p.
  - eapply transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Next Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply implement_box_eval; cbn; eauto.
  all: reflexivity.
Qed.

#[global]
Instance implement_box_extends (efl := extraction_env_flags_mlf) :
   TransformExt.t (implement_box_transformation) extends_eprogram extends_eprogram.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /= /implement_box_program /=.
  split => /=.
  eapply (implement_box_env_extends). all: try reflexivity.
  exact ext.
  apply pr.
  apply pr'.
  now rewrite -eq.
Qed.

#[local] Obligation Tactic := program_simpl.

Definition annotate_decl Γ (d : EAst.global_decl) :=
  match d with
    | EAst.ConstantDecl (EAst.Build_constant_body (Some b)) => EAst.ConstantDecl (EAst.Build_constant_body (Some (annotate Γ b)))
  | d => d
  end.

Lemma lookup_env_annotate {Σ : EAst.global_declarations} Γ kn :
  EGlobalEnv.lookup_env (annotate_env Γ Σ) kn =
  option_map (annotate_decl Γ) (EGlobalEnv.lookup_env Σ kn).
Proof.
  induction Σ at 1 2; simpl; auto.
  destruct a. destruct g0. destruct c. destruct cst_body0.
  all: cbn; case: eqb_spec => //.
Qed.

Lemma lookup_inductive_annotate_env (Σ : EAst.global_declarations) Γ (ind : inductive) :
  EGlobalEnv.lookup_inductive (annotate_env Γ Σ) ind =
  EGlobalEnv.lookup_inductive Σ ind.
Proof.
  unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive.
  rewrite !lookup_env_annotate.
  destruct EGlobalEnv.lookup_env; try reflexivity.
  cbn.
  destruct g; cbn; try reflexivity.
  destruct c; cbn; try reflexivity.
  destruct cst_body0; reflexivity.
Qed.

Lemma annotate_env_fresh(k : kername) (Σ : list (kername × EAst.global_decl)) :
  EGlobalEnv.fresh_global k Σ -> EGlobalEnv.fresh_global k (annotate_env [] Σ).
Proof.
  induction 1.
  - econstructor.
  - cbn. destruct x. destruct g. destruct c.
    destruct cst_body0.
    all: econstructor; eauto.
Qed.

Arguments wellformed : clear implicits.
Arguments wf_glob : clear implicits.

Lemma name_annotation_good_for_extraction:
  forall input : program EAst.global_declarations EAst.term,
    good_for_extraction (switch_off_box extraction_env_flags_mlf) input ->
    wf_eprogram (switch_off_box extraction_env_flags_mlf) input ->
    good_for_extraction named_extraction_env_flags_mlf (annotate_env [] input.1, annotate [] input.2).
Proof.
  intros input H H0.
  destruct input as [Σ s].
  split.
  + intros. eapply few_enough_blocks. eassumption.
    unfold lookup_constructor_args in *.
    instantiate (1 := i).
    erewrite <- lookup_inductive_annotate_env.
    eassumption.
  + intros. eapply few_enough_constructors. eassumption.
    unfold lookup_constructor_args in *.
    instantiate (1 := mb). instantiate (1 := i).
    erewrite <- lookup_inductive_annotate_env.
    eassumption.
  + intros.
    rewrite lookup_inductive_annotate_env in H1.
    eapply few_enough_arguments_in_constructors; eauto.
  + cbn. destruct H0.
    clear H1. cbn in *. clear H. induction Σ; cbn.
  - econstructor.
  - destruct a. destruct g. destruct c. destruct cst_body0.
    * invs H0. constructor; eauto.
      cbn in *. now eapply (wellformed_annotate' _ _ [] []) in H4.
      cbn in *. now eapply annotate_env_fresh.
    * invs H0. econstructor; eauto.
      now eapply annotate_env_fresh.
    * invs H0. econstructor; eauto.
      now eapply annotate_env_fresh.
    + cbn. destruct H0. eapply wellformed_annotate' with (Γ := nil) (Γ' := nil) in H1; auto.
      red. auto.
Qed.

Program Definition name_annotation : Transform.t EAst.global_declarations (list (Kernames.kername × EAst.global_decl))
  EAst.term EAst.term _ EWcbvEvalNamed.value
  (EProgram.eval_eprogram extraction_wcbv_flags) (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) :=
  {| name := "annotate names";
      pre := fun p =>  good_for_extraction (switch_off_box extraction_env_flags_mlf) p /\
        EProgram.wf_eprogram (switch_off_box extraction_env_flags_mlf) p ;
      transform p _ := (annotate_env [] p.1, annotate [] p.2) ;
      post := fun p => good_for_extraction named_extraction_env_flags_mlf p /\
                      exists t, wellformed (switch_off_box extraction_env_flags_mlf) p.1 0 t
                      /\ ∥represents [] [] p.2 t∥ ;
      obseq p _ p' v v' := ∥ represents_value v' v∥ |}.
Next Obligation.
  split.
  { now eapply name_annotation_good_for_extraction. }
  destruct input as [Σ s].
  destruct H0 as [HΣ Hs]. cbn. exists s.
  cbn in *. split.
  2:{ sq. eapply (nclosed_represents (switch_off_box extraction_env_flags_mlf)); cbn; eauto. }
  clear - Hs. revert Hs. generalize 0. intros.
  induction s using EInduction.term_forall_list_ind in n, Hs |- *; cbn in *; eauto; rtoProp; eauto.
  all: try now rtoProp; eauto.
  - unfold EGlobalEnv.lookup_constant in *. rewrite lookup_env_annotate. destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
  - unfold EGlobalEnv.lookup_constructor_pars_args, EGlobalEnv.lookup_constructor, EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *. rewrite lookup_env_annotate.
    destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
    destruct nth_error; cbn in *; try congruence.
    destruct nth_error; cbn in *; try congruence.
    repeat split; eauto.
    solve_all.
  - revert H; unfold wf_brs. unfold EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive in *.
    rewrite lookup_env_annotate.
    destruct EGlobalEnv.lookup_env as [ [[ [] ] | ] | ]; cbn in *; eauto.
    destruct nth_error; cbn in *; try congruence.
    repeat split; eauto.
    solve_all.
  - solve_all. unfold wf_fix in *. rtoProp. solve_all.
  - solve_all. destruct p as [? []]; cbn in *; eauto.
Qed.
Next Obligation.
  red. intros. destruct pr as [_ pr]. red in H. sq.
  unshelve eapply (eval_to_eval_named_full (switch_off_box extraction_env_flags_mlf)) in H as [v_ Hv].
  3-9:eauto.
  - shelve.
  - exists v_. repeat split; sq. cbn. eapply Hv. eapply Hv.
  - eapply pr.
  - destruct pr. clear H1 H.
    generalize (@nil Kernames.ident) at 2. induction H0; cbn; intros.
    + econstructor.
    + destruct d. destruct c. destruct cst_body0.
      * econstructor; eauto. cbn in *. eapply sunny_subset. eapply sunny_annotate.
        intros ? [].
      * econstructor; eauto. cbn in *. eauto.
      * econstructor; eauto. cbn in *. eauto.
  - destruct pr. clear - H0.
    induction p.1.
    + cbn. econstructor.
    + cbn. destruct a as [? [ [[]]| ]]; intros; econstructor; eauto; cbn; eauto.
      2-4: eapply IHg; now invs H0.
      split; eauto. eexists. split. cbn. reflexivity.
      eapply (nclosed_represents (switch_off_box extraction_env_flags_mlf)); cbn => //. invs H0. cbn in *. eauto.
  - eapply pr.
Qed.

Lemma annotate_extends (efl := switch_off_box extraction_env_flags_mlf) Σ Σ' :
   EGlobalEnv.extends Σ Σ' ->
   EGlobalEnv.extends (annotate_env [] Σ) (annotate_env [] Σ').
Proof.
  red. intros ext kn decl Hdecl. rewrite lookup_env_annotate in Hdecl.
  rewrite lookup_env_annotate. eapply option_map_Some in Hdecl as [? [? ?]].
  erewrite ext; cbn; eauto. now f_equal.
Qed.

Program Definition compile_to_malfunction `{Heap}:
  Transform.t (list (Kernames.kername × EAst.global_decl)) _ _ _
    EWcbvEvalNamed.value SemanticsSpec.value
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to Malfunction";
      pre := fun p =>   EWellformed.wf_glob named_extraction_env_flags_mlf p.1 /\ (exists t, EWellformed.wellformed (switch_off_box extraction_env_flags_mlf) p.1 0 t /\ ∥ represents [] [] p.2 t∥) /\
                       good_for_extraction named_extraction_env_flags_mlf p ;
      transform p _ := compile_program p ;
      post := fun p => CompileCorrect.wellformed (map (fun '(i,_) => i) p.1) [] p.2 ;
      obseq p _ p' v v' := forall (hh:heap), v' = CompileCorrect.compile_value p.1 v
  |}.
Next Obligation. sq.
  erewrite (map_ext _ fst).
  eapply (compile_wellformed _ 0 _ H2).
  eapply H3.
  eapply H4. eapply H5.
  intros. now destruct x.
Qed.
Next Obligation.
  red. intros. exists (compile_value p.1 v); eauto.
Qed.

Program Definition post_verified_named_erasure_pipeline `{Heap}:
 Transform.t EAst.global_declarations _ _ _ _ EWcbvEvalNamed.value
 (eval_eprogram EConstructorsAsBlocks.block_wcbv_flags)
 (fun p v => ∥ EWcbvEvalNamed.eval p.1 [] p.2 v ∥)  :=
  enforce_extraction_conditions ▷
  implement_box_transformation ▷
  name_annotation.

Program Definition verified_named_erasure_pipeline `{Heap}:
 Transform.t global_env_ext_map _ _ _ _ EWcbvEvalNamed.value
             PCUICTransform.eval_pcuic_program
             (fun p v => ∥ EWcbvEvalNamed.eval p.1 [] p.2 v ∥) :=
  verified_erasure_pipeline ▷
  post_verified_named_erasure_pipeline.

Program Definition verified_malfunction_pipeline `{Heap} :
 Transform.t global_env_ext_map _ _ _ _ SemanticsSpec.value
             PCUICTransform.eval_pcuic_program
             (fun _ _ => True) :=
  verified_named_erasure_pipeline ▷
  compile_to_malfunction.
Next Obligation.
  cbn. intros.
  destruct p as [Σ t]. split. apply H1. sq. split. 2: eauto.
  eexists. split. 2:sq. all:eauto.
Qed.

Section compile_malfunction_pipeline.

  Variable HP : Pointer.
  Variable HH : Heap.

  Variable Σ : global_env_ext_map.
  Variable t : term.
  Variable T : term.

  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.
  Variable expt : expanded Σ.1 [] t.
  Variable typing : ∥Σ ;;; [] |- t : T∥.

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Definition compile_malfunction_pipeline := transform verified_malfunction_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing _).

End compile_malfunction_pipeline.

Arguments compile_malfunction_pipeline {_ _ _ _ _ _} _ _ _ {_}.

Local Existing Instance CanonicalHeap.
Local Existing Instance CanonicalPointer.

Program Definition verified_typed_erasure_pipeline_unsafe econf :=
  verified_typed_erasure_pipeline econf ▷ (optional_unsafe_transforms econf).
Next Obligation.
  unfold optional_unsafe_transforms, optional_self_transform in H |- *.
  destruct enable_unsafe as [[] [] [] []] => //.
Qed.

(* This also optionally runs typed erasure and/or the cofix to fix translation *)
Program Definition switchable_erasure_pipeline econf :=
  if econf.(enable_typed_erasure) then verified_typed_erasure_pipeline_unsafe econf
  else verified_erasure_pipeline_mapping ▷ (optional_unsafe_transforms econf).
Next Obligation.
Proof.
  unfold optional_unsafe_transforms, optional_self_transform.
  destruct enable_unsafe as [[] ? ? ?] => //.
Qed.

Program Definition malfunction_pipeline
  (config : malfunction_pipeline_config) :
  Transform.t _ _ _ _ _ _ eval_template_program_mapping
             (fun _ _ => True) :=
  pre_erasure_pipeline_mapping ▷
  switchable_erasure_pipeline config ▷
  post_verified_named_erasure_pipeline ▷
  compile_to_malfunction.
Next Obligation.
  unfold switchable_erasure_pipeline.
  destruct enable_typed_erasure => //.
Qed.
Next Obligation.
  intuition auto; destruct H; intuition eauto.
Qed.

Fixpoint extract_names (t : Ast.term) : list ident :=
  match t with
  | Ast.tConst kn _ => [Kernames.string_of_kername kn]
  | Ast.tApp (Ast.tConstruct _ _ _) [_ ; _ ; l ; Ast.tConst kn _ ] => (Kernames.string_of_kername kn) :: extract_names l
  | _ => []
  end.

Axiom trust_coq_kernel : forall conf p, pre (malfunction_pipeline conf) (conf.(reorder_cstrs), p).

Definition compile_malfunction_gen config (pt : program_type) (p : Ast.Env.program) : list string * string := (* Exported names, code *)
  let nms := extract_names p.2 in
  let p' := run (malfunction_pipeline config) (config.(reorder_cstrs), p) (trust_coq_kernel config p) in
  let serialize p_c := @to_string _ (Serialize_module config.(prims) pt (rev nms)) p_c in
  let code := time "Pretty printing"%bs serialize p' in
  (nms, code).

Definition default_malfunction_config : malfunction_pipeline_config :=
  {| erasure_config := safe_erasure_config; reorder_cstrs := []; prims := [] |}.

Definition compile_malfunction p :=
  (compile_malfunction_gen default_malfunction_config Standalone p).2.
