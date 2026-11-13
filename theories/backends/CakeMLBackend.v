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

(** The (partly verified) part of the backend: name annotation and
    compilation to CakeML.  As in [OCamlBackend], we do not use
    [enforce_extraction_conditions] (whose postcondition rests on the false
    [assume_can_be_extracted] and, allowing boxes, does not imply the
    precondition of [name_annotation]) but check the precondition of
    [name_annotation] directly ([cakeml_check]), and warn when it fails
    ([extract_cakeml_verified]). *)
(** CakeML's own [compile_to_malfunction] transform has an [Admitted]
    obligation.  It only claims [True] about the result, so this copy with the
    same compilation function proves it. *)
Program Definition compile_to_cakeml :
  Transform.t (list (Kernames.kername × EAst.global_decl)) _ _ _
    EWcbvEvalNamed.value CakeML.CakeML.namespace.val
    (fun p v => ∥EWcbvEvalNamed.eval p.1 [] p.2 v∥) (fun _ _ => True) :=
  {| name := "compile to CakeML";
     pre := fun _ => True;
     transform p _ := CakeML.Backend.Compile.compile_program p;
     post := fun _ => True;
     obseq _ _ _ _ _ := True |}.
Next Obligation.
  intros. now exists (CakeML.CakeML.namespace.Conv None []).
Qed.

Program Definition cakeml_pipeline :
  Transform.t _ _ _ _ _ _ (EProgram.eval_eprogram final_wcbv_flags) (fun _ _ => True) :=
  name_annotation ▷
  compile_to_cakeml.

Definition print_program nms p :=
  let serialize p_c := @to_string _ (Serialize_module (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

Definition cakeml_check (p : EAst.program) : result' unit :=
  @ExtractionCheck.check_extractable CakeML.Backend.Compile.blocks_until 200
    Uint63.wB (Uint63.to_Z array_length)
    (EImplementBox.switch_off_box extraction_env_flags_mlf) p.

Lemma cakeml_check_sound p :
  bool_of_result (cakeml_check p) = true -> pre cakeml_pipeline p.
Proof.
  intros h. apply ExtractionCheck.check_extractable_sound in h as [hwf hi].
  split; [|exact hwf]. destruct hwf as [hg ht].
  constructor; [| | |exact hg|exact ht].
  - intros i args. unfold CakeML.Backend.Compile.lookup_constructor_args.
    destruct EGlobalEnv.lookup_inductive as [[mb ob]|] eqn:hl; [|discriminate].
    intros [= <-].
    exact (proj1 (ExtractionCheck.check_inductive_body_spec _ _ _ _ _
      (ExtractionCheck.check_inductives_lookup _ _ _ _ _ _ _ _ hi hl))).
  - intros i mb ob hl.
    exact (proj1 (proj2 (ExtractionCheck.check_inductive_body_spec _ _ _ _ _
      (ExtractionCheck.check_inductives_lookup _ _ _ _ _ _ _ _ hi hl)))).
  - intros i mb ob hl.
    exact (proj2 (proj2 (ExtractionCheck.check_inductive_body_spec _ _ _ _ _
      (ExtractionCheck.check_inductives_lookup _ _ _ _ _ _ _ _ hi hl)))).
Qed.

(** The compilation function of [cakeml_pipeline].  The [transform]s of
    [name_annotation] and [compile_to_cakeml] do not use the proof of their
    precondition, so [cakeml_pipeline] computes [compile_cakeml] on every
    program that satisfies the precondition. *)
Definition compile_cakeml (p : EAst.program) :=
  CakeML.Backend.Compile.compile_program
    (EWcbvEvalNamed.annotate_env [] p.1, EWcbvEvalNamed.annotate [] p.2).

Lemma run_cakeml_pipeline p pr :
  run cakeml_pipeline p pr = compile_cakeml p.
Proof. reflexivity. Qed.

(** [extract_cakeml] compiles every program with [compile_cakeml].  It runs
    [cakeml_check] only to report a warning when the program is outside the
    precondition of [cakeml_pipeline], see [extract_cakeml_verified]. *)
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
    of [cakeml_pipeline] at a proof of its precondition. *)
Lemma extract_cakeml_verified remaps custom_attr opts file_name p warnings out :
  extract_cakeml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] ->
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  exists pr : pre cakeml_pipeline p0,
    out = let '(dtypes, env, main) := run cakeml_pipeline p0 pr in
          print_program (extract_names (snd p))
            (dtypes, ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) env, main).
Proof.
  intros h hw. unfold extract_cakeml in h. cbv zeta.
  destruct (compile_cakeml _) as [[dtypes env] main] eqn:hc.
  injection h as <- <-.
  apply ExtractionCheck.unverified_warning_nil in hw.
  exists (cakeml_check_sound _ hw). now rewrite run_cakeml_pipeline, hc.
Qed.

(** [extract_cakeml] reports a warning exactly when [cakeml_check] fails. *)
Lemma extract_cakeml_warnings remaps custom_attr opts file_name p warnings out :
  extract_cakeml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] <-> bool_of_result (cakeml_check (ExtractionCheck.fill_axioms p.1, p.2)) = true.
Proof.
  intros h. unfold extract_cakeml in h. destruct compile_cakeml as [[dtypes env] main].
  injection h as <- _. apply ExtractionCheck.unverified_warning_nil.
Qed.
