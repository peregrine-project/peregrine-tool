(** * The input front end of the pipeline

    [peregrine_pipeline] takes the input program as a string. This file shows, for
    the pipeline [peregrine_pipeline_gen] at any implementation of the guard
    condition ([peregrine_pipeline] is its instance, [peregrine_pipeline_instance]), that
    - the pipeline only depends on the parsed program ([peregrine_pipeline_parsed]),
    - on the serialization of a program [p0] (with escapable strings, see
      [SerializeRoundtrip.strings_ok]) it is the pipeline run on [p0]
      ([peregrine_pipeline_string_of_PAst]), and
    - a successfully parsed program is determined by the s-expression read from the
      input ([parse_ast_sound]), and is the unique program whose printing parses to it.

    The same is shown for the configuration file and attribute files. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.SafeChecker Require PCUICWfEnvImpl.
From CeresBS Require Import Ceres CeresParser.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts CheckWf RecursorInlining AutoInlining Pipeline.
From Peregrine Require NameSanitize Transforms.
From Peregrine Require Import Utils PipelineWf.
From Peregrine Require Import Serialize Deserialize SerializeComplete SerializeRoundtrip.
From Peregrine Require Import SerializeConfig SerializePAst.

Import MonadNotation.
Local Open Scope bs_scope.

(** The pipeline after parsing the input program (same code as [peregrine_pipeline_gen]
    minus its first line; [peregrine_pipeline_parsed] checks this by [reflexivity]). *)
Definition peregrine_pipeline_ast {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (p : PAst) (f : string) : extraction_result :=
  cp <- peregrine_front c attrs inline_recursors inl p;;
  peregrine_back lbox f cp.

Definition peregrine_validate_ast (c : string + config') (attrs : list string) (p : PAst) : result' unit :=
  c <- get_config c attrs;;
  check_wf p.

(** ** Parsing the input program *)

Lemma parse_ast_string_of_PAst (p0 : PAst) :
  strings_ok p0 = true -> parse_ast (Serialize.string_of_PAst p0) = Ok p0.
Proof.
  intros H. unfold parse_ast. rewrite PAst_of_string_complete by exact H. reflexivity.
Qed.

(** Trailing whitespace (e.g. a final newline in the file) is accepted too. *)
Lemma parse_ast_string_of_PAst_ws (p0 : PAst) ws :
  strings_ok p0 = true -> CeresString.string_forall CeresString.is_whitespace ws = true ->
  parse_ast (Serialize.string_of_PAst p0 ++ ws) = Ok p0.
Proof.
  intros H Hws. unfold parse_ast. rewrite PAst_of_string_complete_ws by assumption. reflexivity.
Qed.

(** Soundness: the parsed program is the one whose serialization is the
    s-expression in the input. *)
Lemma parse_ast_sound (s : string) (p : PAst) :
  parse_ast s = Ok p -> parse_sexp s = inr (to_sexp p).
Proof.
  unfold parse_ast. destruct PAst_of_string eqn:E; intros [=]; subst.
  now apply PAst_of_string_sound.
Qed.

(** Uniqueness: two inputs that read as the same s-expression parse to the same
    program; the serialization of a parsed program parses back to it. *)
Lemma parse_ast_unique (s s' : string) (p p' : PAst) :
  parse_ast s = Ok p -> parse_ast s' = Ok p' -> parse_sexp s = parse_sexp s' -> p = p'.
Proof.
  intros H H' Hs. apply parse_ast_sound in H, H'. rewrite H, H' in Hs.
  injection Hs as Hs.
  assert (Ep : @from_sexp PAst _ (to_sexp p) = inr p) by exact (complete_class nil _).
  assert (Ep' : @from_sexp PAst _ (to_sexp p') = inr p') by exact (complete_class nil _).
  rewrite Hs, Ep' in Ep. now injection Ep.
Qed.

Lemma parse_ast_canonical (s : string) (p : PAst) :
  parse_ast s = Ok p -> strings_ok p = true -> parse_ast (Serialize.string_of_PAst p) = Ok p.
Proof. intros _. apply parse_ast_string_of_PAst. Qed.

(** ** The pipeline only depends on the parsed program *)

Lemma peregrine_pipeline_parsed {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox s f p :
  parse_ast s = Ok p ->
  peregrine_pipeline_gen c attrs ir io lbox s f = peregrine_pipeline_ast c attrs ir io lbox p f.
Proof. intros H. unfold peregrine_pipeline_gen. rewrite H. reflexivity. Qed.

Lemma peregrine_pipeline_parse_error {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox s f e :
  parse_ast s = Err e -> peregrine_pipeline_gen c attrs ir io lbox s f = Err e.
Proof. intros H. unfold peregrine_pipeline_gen. rewrite H. reflexivity. Qed.

(** Main statement: running the tool on the serialization of [p0] is running the
    pipeline on [p0]. *)
Theorem peregrine_pipeline_string_of_PAst {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox (p0 : PAst) f :
  strings_ok p0 = true ->
  peregrine_pipeline_gen c attrs ir io lbox (Serialize.string_of_PAst p0) f = peregrine_pipeline_ast c attrs ir io lbox p0 f.
Proof. intros H. apply peregrine_pipeline_parsed, parse_ast_string_of_PAst, H. Qed.

Theorem peregrine_validate_string_of_PAst c attrs (p0 : PAst) :
  strings_ok p0 = true ->
  peregrine_validate c attrs (Serialize.string_of_PAst p0) = peregrine_validate_ast c attrs p0.
Proof.
  intros H. unfold peregrine_validate. rewrite parse_ast_string_of_PAst by exact H. reflexivity.
Qed.

(** ** Configuration and attribute files *)

Lemma parse_config_string_of_config (c0 : config') :
  strings_ok c0 = true -> parse_config (Serialize.string_of_config c0) = Ok (mk_config c0).
Proof.
  intros H. unfold parse_config. rewrite config_of_string_complete by exact H. reflexivity.
Qed.

Lemma parse_attribute_string_of_attributes_config (a0 : attributes_config) :
  strings_ok a0 = true -> parse_attribute (Serialize.string_of_attributes_config a0) = Ok a0.
Proof.
  intros H. unfold parse_attribute. rewrite attributes_config_of_string_complete by exact H.
  reflexivity.
Qed.

Lemma parse_attributes_string_of_attributes_config (as0 : list attributes_config) :
  forallb strings_ok as0 = true ->
  parse_attributes (map Serialize.string_of_attributes_config as0) = Ok as0.
Proof.
  unfold parse_attributes. induction as0 as [|a as0 IH]; [reflexivity|].
  cbn [forallb map monad_map]. intros [Ha Has]%andb_true_iff.
  rewrite parse_attribute_string_of_attributes_config by exact Ha.
  rewrite IH by exact Has. reflexivity.
Qed.

(** A printed configuration file behaves as passing the configuration directly. *)
Theorem get_config_string_of_config (c0 : config') attrs :
  strings_ok c0 = true ->
  get_config (inl (Serialize.string_of_config c0)) attrs = get_config (inr c0) attrs.
Proof.
  intros H. unfold get_config. rewrite parse_config_string_of_config by exact H. reflexivity.
Qed.

Theorem get_config_printed (c0 : config') (as0 : list attributes_config) :
  strings_ok c0 = true -> forallb strings_ok as0 = true ->
  get_config (inl (Serialize.string_of_config c0)) (map Serialize.string_of_attributes_config as0) =
  Ok (let c := mk_config c0 in
      if 0 <? List.length as0 then merge_attributes_config c as0 else c).
Proof.
  intros H Has. unfold get_config. rewrite parse_config_string_of_config by exact H.
  cbn. rewrite parse_attributes_string_of_attributes_config by exact Has.
  cbn. destruct (0 <? List.length as0); reflexivity.
Qed.

(** All inputs printed. *)
Theorem peregrine_pipeline_printed {guard : PCUICWfEnvImpl.abstract_guard_impl} (c0 : config') (as0 : list attributes_config) ir io lbox (p0 : PAst) f :
  strings_ok p0 = true -> strings_ok c0 = true -> forallb strings_ok as0 = true ->
  peregrine_pipeline_gen (inl (Serialize.string_of_config c0)) (map Serialize.string_of_attributes_config as0) ir io lbox
    (Serialize.string_of_PAst p0) f =
  peregrine_pipeline_ast (inr c0) (map Serialize.string_of_attributes_config as0) ir io lbox p0 f.
Proof.
  intros Hp Hc Has. rewrite peregrine_pipeline_string_of_PAst by exact Hp.
  unfold peregrine_pipeline_ast, peregrine_front. rewrite get_config_string_of_config by exact Hc. reflexivity.
Qed.

(** ** Warnings about skipped optimizations

    When MetaRocq's [check_dearging_precond] fails on typed input, dearging
    is the identity (see [Transforms.dearging_checks_transform_mapping']); the
    program is still compiled correctly, but unused arguments are kept.
    [peregrine_pipeline_warn_gen] runs [peregrine_pipeline_gen] and, when it
    succeeds, adds a warning saying so ([dearging_warnings]).  These warnings
    are separate from the backends' warnings in [extraction_result], which
    report programs outside verified extraction's correctness theorem: a
    skipped optimization does not affect correctness, so [--strict-verified]
    does not reject it.  The warnings are a diagnostic: nothing is proved about
    them, and [peregrine_pipeline_warn_result] shows that the extracted program
    is the one of [peregrine_pipeline_gen]. *)

(** The warning for typed input, with the configuration of [apply_transforms],
    on the result of [peregrine_front].  Untyped input given to a typed
    backend is not checked: its typed environment is only inferred inside
    [apply_transforms]. *)
Definition dearging_warnings {guard : PCUICWfEnvImpl.abstract_guard_impl} (c : config) (p : PAst)
  (hwf : wf_PAst p) : list string :=
  match p as p return wf_PAst p -> list string with
  | Typed env t => fun hwf =>
    match Transforms.typed_dearging_failure (mk_opts c (needs_typed c) (remap_masks c false env))
            (mk_cstr_reorders c) (drop_remapped_bodies c env, PAst_main t)
            (wf_drop_remapped_bodies c env (PAst_main t) hwf) with
    | Some why =>
      ["dearging was skipped, so unused arguments are kept (MetaRocq's check_dearging_precond failed: " ++ why ++ ")"]
    | None => []
    end
  | Untyped _ _ => fun _ => []
  end hwf.

Definition peregrine_pipeline_warn_gen {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (s : string) (f : string)
  : result' (list string * (list string * extracted_program)) :=
  p <- parse_ast s;;
  cp <- peregrine_front c attrs inline_recursors inl p;;
  r <- peregrine_back lbox f cp;;
  let ws := dearging_warnings (proj1_sig cp).1 (proj1_sig cp).2 (proj2_sig cp) in
  Ok (ws, r).

Lemma peregrine_pipeline_warn_result {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox s f :
  (r <- peregrine_pipeline_warn_gen c attrs ir io lbox s f;; Ok r.2) =
  peregrine_pipeline_gen c attrs ir io lbox s f.
Proof.
  unfold peregrine_pipeline_warn_gen. destruct (parse_ast s) as [p|e] eqn:E; cbn.
  - rewrite (peregrine_pipeline_parsed c attrs ir io lbox s f p E).
    unfold peregrine_pipeline_ast.
    destruct peregrine_front; cbn; [|reflexivity].
    now destruct peregrine_back.
  - symmetry. now apply peregrine_pipeline_parse_error.
Qed.

(** The executable entry point (extracted in Extraction.v). *)
Definition peregrine_pipeline_warn : forall (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (p : string) (f : string),
  result' (list string * (list string * extracted_program)) :=
  @peregrine_pipeline_warn_gen MetaRocq.ErasurePlugin.Erasure.fake_guard_impl.
