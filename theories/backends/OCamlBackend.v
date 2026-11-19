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
From Malfunction Require Import Pipeline.
From Malfunction Require Import Serialize.
From Malfunction Require Import SemanticsSpec.
From Stdlib Require Import List.
From CeresBS Require Import CeresSerialize.

Import ListNotations.
Import MonadNotation.
Import Common.Transform.Transform.

Local Open Scope bs_scope.



Definition default_ocaml_config := {|
  Config.program_type := Malfunction.Serialize.Standalone
|}.

Definition ocaml_phases := {|
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

Local Existing Instance CanonicalHeap.
Local Existing Instance CanonicalPointer.

(** The verified part of the backend: name annotation and compilation to
    Malfunction.  rocq-verified-extraction prefixes these with
    [enforce_extraction_conditions], whose postcondition (resting on the false
    [assume_can_be_extracted]) does not imply the precondition of
    [name_annotation] anyway: it allows boxes, while [name_annotation] needs a
    box-free program.  Instead, [extract_ocaml] checks the precondition of
    [name_annotation] directly ([malfunction_check]), and warns when it fails
    ([extract_ocaml_verified]). *)
Program Definition malfunction_pipeline :
  Transform.t _ _ _ _ _ _ (EProgram.eval_eprogram final_wcbv_flags) (fun _ _ => True) :=
  name_annotation ▷
  compile_to_malfunction.
Next Obligation.
  split; [exact (right_flags_in_glob _ _ H)|]. split; [now exists H0|exact H].
Qed.

Definition print_program prims pt nms p :=
  let serialize p_c := @to_string _ (Serialize_module prims pt (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

Definition mk_remaps (rs : constant_remappings) : Malfunction.primitives :=
  map (fun '(kn, r) =>
      let '(m, s) := split_name r.(re_const_s) in
      (string_of_kername kn, Malfunction.Global m s)
  ) rs.
(* TODO: support Malfuntion prim_def.Primtive & prim_def.Erased *)
(* TODO: collect list of packages for compiling *)



Definition malfunction_check (p : EAst.program) : result' unit :=
  @ExtractionCheck.check_extractable Malfunction.Compile.blocks_until 200
    Malfunction.Int63.wB (Uint63.to_Z array_length)
    (EImplementBox.switch_off_box extraction_env_flags_mlf) p.

Lemma malfunction_check_sound p :
  bool_of_result (malfunction_check p) = true -> pre malfunction_pipeline p.
Proof.
  intros h. apply ExtractionCheck.check_extractable_sound in h as [hwf hi].
  split; [|exact hwf]. destruct hwf as [hg ht].
  constructor; [| | |exact hg|exact ht].
  - intros i args. unfold Malfunction.Compile.lookup_constructor_args.
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

(** The compilation function of [malfunction_pipeline].  The [transform]s of
    [name_annotation] and [compile_to_malfunction] do not use the proof of
    their precondition, so [malfunction_pipeline] computes [compile_ocaml] on
    every program that satisfies the precondition. *)
Definition compile_ocaml (p : EAst.program) : Malfunction.Malfunction.program :=
  Malfunction.Compile.compile_program
    (EWcbvEvalNamed.annotate_env [] p.1, EWcbvEvalNamed.annotate [] p.2).

Lemma run_malfunction_pipeline p pr :
  run malfunction_pipeline p pr = compile_ocaml p.
Proof. reflexivity. Qed.

(** [extract_ocaml] compiles every program with [compile_ocaml].  It runs
    [malfunction_check] only to report a warning when the program is outside
    the precondition of [malfunction_pipeline], see [extract_ocaml_verified]. *)
Definition extract_ocaml (remaps : constant_remappings)
                         (custom_attr : custom_attributes)
                         (opts : ocaml_config)
                         (file_name : string)
                         (p : EAst.program)
                         : result' (list string * (list string * string)) :=
  let nms := extract_names (snd p) in
  let remaps := mk_remaps remaps in
  (* Axioms get placeholder bodies for the verified passes, see
     [ExtractionCheck.fill_axioms]. *)
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  let warnings := ExtractionCheck.unverified_warning "OCaml" (malfunction_check p0) in
  let m := compile_ocaml p0 in
  let m := (ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) m.1, m.2) in
  Ok (warnings, print_program remaps opts.(Config.program_type) nms m).

(** When [extract_ocaml] reports no warning, its output is the printed result
    of [malfunction_pipeline], the pipeline of verified extraction's
    correctness theorem, at a proof of its precondition. *)
Lemma extract_ocaml_verified remaps custom_attr opts file_name p warnings out :
  extract_ocaml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] ->
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  exists pr : pre malfunction_pipeline p0,
    let m := run malfunction_pipeline p0 pr in
    out = print_program (mk_remaps remaps) opts.(Config.program_type) (extract_names (snd p))
            (ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) m.1, m.2).
Proof.
  intros h hw. unfold extract_ocaml in h. injection h as <- <-. cbv zeta.
  apply ExtractionCheck.unverified_warning_nil in hw.
  now exists (malfunction_check_sound _ hw).
Qed.

(** [extract_ocaml] reports a warning exactly when [malfunction_check] fails. *)
Lemma extract_ocaml_warnings remaps custom_attr opts file_name p warnings out :
  extract_ocaml remaps custom_attr opts file_name p = Ok (warnings, out) ->
  warnings = [] <-> bool_of_result (malfunction_check (ExtractionCheck.fill_axioms p.1, p.2)) = true.
Proof.
  intros h. unfold extract_ocaml in h. injection h as <- _.
  apply ExtractionCheck.unverified_warning_nil.
Qed.
