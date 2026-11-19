From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.ErasurePlugin Require Import ETransform.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require CheckWf ExtractionCheck.
From Stdlib Require Import List.
From CeresBS Require Import CeresSerialize.
From CakeML.Backend Require Import Pipeline.
From CakeML.Backend Require Import Serialize.
From CakeML.Backend Require CompileCorrect PipelineCorrect.
From CakeML.CakeML Require namespace bigstep.

Import ListNotations.
Import MonadNotation.
Import Common.Transform.Transform.

Local Open Scope bs_scope.



Definition default_cakeml_config := tt.

Definition cakeml_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
  lift_constants_c := Compatible false;
|}.



Fixpoint extract_names (t : EAst.term) : list ident :=
  match t with
  | EAst.tConst kn => [Kernames.string_of_kername kn]
  | EAst.tApp u v => (extract_names u) ++ extract_names v
  | _ => []
  end.

(** The verified part of the backend: name annotation and compilation to
    CakeML.  As in [OCamlBackend], we do not use [enforce_extraction_conditions]
    but check the precondition of [name_annotation] directly ([cakeml_check]),
    and warn when it fails ([extract_cakeml_verified]). *)

(** The correctness relation of the compilation to CakeML
    ([CakeML.Backend.PipelineCorrect.cakeml_correct_named_vrel]).  The emitted
    program [p'] is a list of datatype declarations, a list of [Dlet]
    declarations and a main expression.  If the names used by the emitted
    program do not clash ([CompileCorrect.names_ok p], checked by
    [cakeml_check]), then for every run of the declarations
    ([eval_program_decls n0 env0]: the [Dtype] blocks allocate type stamps
    starting from [n0] and extend [env0], then the [Dlet]s are evaluated), the
    main expression evaluates to a CakeML value related to the λ□ value [v].  On
    first-order values the relation is equality with
    [CompileCorrect.compile_value] ([CompileCorrect.vrel_fo]). *)
Definition cakeml_obseq (p : EProgram.eprogram)
    (p' : (list (list (string * list (string * nat))) * list (string * option CakeML.CakeML.ast.exp)) * CakeML.CakeML.ast.exp)
    (v : EWcbvEvalNamed.value) : Prop :=
  CompileCorrect.names_ok p = true ->
  forall n0 env0 genv,
    CompileCorrect.eval_program_decls n0 env0 p'.1 genv ->
    exists w, bigstep.evaluate genv p'.2 (namespace.Rval w) /\
      CompileCorrect.vrel p.1 (namespace.c _ genv) (CompileCorrect.type_stamp n0 p.1) v w.

Program Definition compile_to_cakeml :
  Transform.t (list (Kernames.kername × EAst.global_decl)) _ _ _
    EWcbvEvalNamed.value CakeML.CakeML.namespace.val
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to CakeML";
     pre := fun p => good_for_extraction named_extraction_env_flags_mlf p;
     transform p _ := CakeML.Backend.Compile.compile_program p;
     post := fun _ => True;
     obseq p _ p' v _ := cakeml_obseq p p' v |}.
Next Obligation.
  exists (CakeML.CakeML.namespace.Conv None []). split; [exact I|].
  intros hnames n0 env0 genv hdecls.
  exact (PipelineCorrect.cakeml_correct_named_vrel p v n0 env0 genv pr hnames H hdecls).
Qed.

Program Definition cakeml_pipeline :
  Transform.t _ _ _ _ _ _ (EProgram.eval_eprogram final_wcbv_flags) (fun _ _ => True) :=
  name_annotation ▷
  compile_to_cakeml.

Definition print_program nms p :=
  let serialize p_c := @to_string _ (Serialize_module (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

(** The program that [name_annotation] hands to [compile_to_cakeml]. *)
Definition annotate_program (p : EAst.program) : EProgram.eprogram :=
  (EWcbvEvalNamed.annotate_env [] p.1, EWcbvEvalNamed.annotate [] p.2).

(** [cakeml_check] decides the precondition of [cakeml_pipeline] and the
    side condition [CompileCorrect.names_ok] of its correctness relation
    ([cakeml_obseq]) on the annotated program. *)
Definition cakeml_check (p : EAst.program) : result' unit :=
  @ExtractionCheck.check_extractable CakeML.Backend.Compile.blocks_until 200
    Uint63.wB (Uint63.to_Z array_length)
    (EImplementBox.switch_off_box extraction_env_flags_mlf) p ;;
  assert' (CompileCorrect.names_ok (annotate_program p))
    (fun _ => "Names in the generated CakeML program may clash (a binder containing '.', two constants or two constructors printed alike, or a case branch whose binders do not fit its constructor)").

Lemma cakeml_check_sound p :
  bool_of_result (cakeml_check p) = true ->
  pre cakeml_pipeline p /\ CompileCorrect.names_ok (annotate_program p) = true.
Proof.
  unfold cakeml_check.
  destruct (ExtractionCheck.check_extractable _ _ _ _ p) eqn:h; cbn; [|discriminate].
  destruct (CompileCorrect.names_ok _) eqn:hn; cbn; [|discriminate]. intros _.
  split; [|reflexivity].
  assert (h' : bool_of_result (@ExtractionCheck.check_extractable CakeML.Backend.Compile.blocks_until 200
    Uint63.wB (Uint63.to_Z array_length)
    (EImplementBox.switch_off_box extraction_env_flags_mlf) p) = true) by now rewrite h.
  apply ExtractionCheck.check_extractable_sound in h' as [hwf _].
  split; [|exact hwf]. destruct hwf as [hg ht]. now constructor.
Qed.

(** The compilation function of [cakeml_pipeline].  The [transform]s of
    [name_annotation] and [compile_to_cakeml] do not use the proof of their
    precondition, so [cakeml_pipeline] computes [compile_cakeml] on every
    program that satisfies the precondition. *)
Definition compile_cakeml (p : EAst.program) :=
  CakeML.Backend.Compile.compile_program (annotate_program p).

Lemma run_cakeml_pipeline p pr :
  run cakeml_pipeline p pr = compile_cakeml p.
Proof. reflexivity. Qed.

(** Correctness of the CakeML backend on a program accepted by [cakeml_check]:
    if [p] evaluates to [v], then [v] is represented by a named value [vn], and
    after any run of the emitted declarations the emitted main expression
    evaluates to a CakeML value related to [vn]. *)
Lemma cakeml_pipeline_correct p v :
  bool_of_result (cakeml_check p) = true ->
  EProgram.eval_eprogram final_wcbv_flags p v ->
  exists vn, ∥ EWcbvEvalNamed.represents_value vn v ∥ /\
    forall n0 env0 genv,
      CompileCorrect.eval_program_decls n0 env0 (compile_cakeml p).1 genv ->
      exists w, bigstep.evaluate genv (compile_cakeml p).2 (namespace.Rval w) /\
        CompileCorrect.vrel (annotate_program p).1 (namespace.c _ genv)
          (CompileCorrect.type_stamp n0 (annotate_program p).1) vn w.
Proof.
  intros hc hev. destruct (cakeml_check_sound p hc) as [pr hn].
  destruct (preservation name_annotation p v pr hev) as (vn & hevn & hobs).
  pose proof (correctness name_annotation p pr) as hpost.
  destruct (preservation compile_to_cakeml _ vn (proj1 hpost) hevn) as (w' & _ & hobs').
  exists vn. split; [exact hobs|]. exact (hobs' hn).
Qed.

(** Constructor trees: first-order values without boxes and primitives.  On
    them the relation of [cakeml_pipeline_correct] is equality with
    [CompileCorrect.compile_value]. *)
Fixpoint fo_cstrb (t : EAst.term) : bool :=
  match t with
  | EAst.tConstruct _ _ args => forallb fo_cstrb args
  | _ => false
  end.

Lemma represents_value_fo_cstr v vn :
  fo_cstrb v = true -> EWcbvEvalNamed.represents_value vn v ->
  vn = PipelineCorrect.eval_fo v /\ CompileCorrect.fo_value vn.
Proof.
  induction v in vn |- * using EInduction.term_forall_list_ind; cbn; try discriminate.
  intros hf hr. inversion hr; subst.
  match goal with H : EPrimitive.All2_Set _ _ _ |- _ => rename H into hvs end.
  assert (h : vs = map PipelineCorrect.eval_fo args /\ Forall CompileCorrect.fo_value vs).
  { clear hr. induction hvs as [|vn' t' vs' ts' hr' hvs' IH] in X, hf |- *; cbn in *; [split; constructor|].
    apply andb_true_iff in hf as [hf1 hf2].
    inversion X as [|? ? hP hX]; subst.
    destruct (hP _ hf1 hr') as [-> hfo].
    destruct (IH hX hf2) as [-> hfos]. split; [reflexivity|now constructor]. }
  destruct h as [-> h]. split; [reflexivity|now constructor].
Qed.

Corollary cakeml_pipeline_correct_fo p v :
  bool_of_result (cakeml_check p) = true ->
  EProgram.eval_eprogram final_wcbv_flags p v ->
  fo_cstrb v = true ->
  forall n0 env0 genv,
    CompileCorrect.eval_program_decls n0 env0 (compile_cakeml p).1 genv ->
    bigstep.evaluate genv (compile_cakeml p).2
      (namespace.Rval (CompileCorrect.compile_value (annotate_program p).1 n0 (PipelineCorrect.eval_fo v))).
Proof.
  intros hc hev hfo n0 env0 genv hd.
  destruct (cakeml_pipeline_correct p v hc hev) as (vn & [hr] & h).
  destruct (represents_value_fo_cstr v vn hfo hr) as [-> hfvn].
  destruct (h n0 env0 genv hd) as (w & hw & hrel).
  rewrite <- (CompileCorrect.vrel_fo _ n0 _ _ _ hfvn hrel). exact hw.
Qed.

(** [extract_cakeml] compiles every program with [compile_cakeml].  It runs
    [cakeml_check] only to report a warning when the program is outside the
    precondition of [cakeml_pipeline] or of its correctness relation, see
    [extract_cakeml_verified]. *)
Definition extract_cakeml (remaps : constant_remappings)
                          (custom_attr : custom_attributes)
                          (opts : cakeml_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' (list string * (list string * string)) :=
  let nms := extract_names (snd p) in
  (* Axioms get placeholder bodies for the verified passes, see
     [ExtractionCheck.fill_axioms]. *)
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  let warnings := ExtractionCheck.unverified_warning "CakeML" (cakeml_check p0) in
  let '(dtypes, env, main) := compile_cakeml p0 in
  Ok (warnings, print_program nms (dtypes, ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) env, main)).

(** When [extract_cakeml] reports no warning, its output is the printed result
    of [cakeml_pipeline] at a proof of its precondition, and the side condition
    of the correctness relation [cakeml_obseq] holds. *)
Lemma extract_cakeml_verified remaps custom_attr opts file_name p warnings out :
  extract_cakeml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] ->
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  exists pr : pre cakeml_pipeline p0,
    CompileCorrect.names_ok (annotate_program p0) = true /\
    out = let '(dtypes, env, main) := run cakeml_pipeline p0 pr in
          print_program (extract_names (snd p))
            (dtypes, ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) env, main).
Proof.
  intros h hw. unfold extract_cakeml in h. cbv zeta.
  destruct (compile_cakeml _) as [[dtypes env] main] eqn:hc.
  injection h as <- <-.
  apply ExtractionCheck.unverified_warning_nil in hw.
  destruct (cakeml_check_sound _ hw) as [pr hn].
  exists pr. split; [exact hn|]. now rewrite run_cakeml_pipeline, hc.
Qed.

(** [extract_cakeml] reports a warning exactly when [cakeml_check] fails. *)
Lemma extract_cakeml_warnings remaps custom_attr opts file_name p warnings out :
  extract_cakeml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] <-> bool_of_result (cakeml_check (ExtractionCheck.fill_axioms p.1, p.2)) = true.
Proof.
  intros h. unfold extract_cakeml in h. destruct compile_cakeml as [[dtypes env] main].
  injection h as <- _. apply ExtractionCheck.unverified_warning_nil.
Qed.
