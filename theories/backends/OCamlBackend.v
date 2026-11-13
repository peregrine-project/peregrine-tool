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
    [name_annotation] directly ([malfunction_check]). *)
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

Definition extract_ocaml (remaps : constant_remappings)
                         (custom_attr : custom_attributes)
                         (opts : ocaml_config)
                         (file_name : string)
                         (p : EAst.program)
                         : result' (list string * string) :=
  let nms := extract_names (snd p) in
  let remaps := mk_remaps remaps in
  (* Axioms get placeholder bodies for the verified passes, see
     [ExtractionCheck.fill_axioms]. *)
  let p0 := (ExtractionCheck.fill_axioms p.1, p.2) in
  m <- map_error (fun e => "OCaml backend: " ++ e)
         (CheckWf.with_check (malfunction_check p0) (malfunction_check_sound p0)
            (run malfunction_pipeline p0)) ;;
  let m := (ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names p.1) m.1, m.2) in
  Ok (print_program remaps opts.(Config.program_type) nms m).
