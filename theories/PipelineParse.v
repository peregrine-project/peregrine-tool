(** * The input front end of the pipeline

    [peregrine_pipeline] takes the input program as a string. This file shows that
    - the pipeline only depends on the parsed program ([peregrine_pipeline_parsed]),
    - on the serialization of a program [p0] (with escapable strings, see
      [SerializeRoundtrip.strings_ok]) it is the pipeline run on [p0]
      ([peregrine_pipeline_string_of_PAst]), and
    - a successfully parsed program is determined by the s-expression read from the
      input ([parse_ast_sound]), and is the unique program whose printing parses to it.

    The same is shown for the configuration file and attribute files. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From CeresBS Require Import Ceres CeresParser.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts CheckWf RecursorInlining AutoInlining Pipeline.
From Peregrine Require NameSanitize.
From Peregrine Require Import Utils.
From Peregrine Require Import Serialize Deserialize SerializeComplete SerializeRoundtrip.
From Peregrine Require Import SerializeConfig SerializePAst.

Import MonadNotation.
Local Open Scope bs_scope.

(** The pipeline after parsing the input program (same code as [peregrine_pipeline]
    minus its first line; [peregrine_pipeline_parsed] checks this by [reflexivity]). *)
Definition peregrine_pipeline_ast (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (p : PAst) (f : string) : extraction_result :=
  c <- get_config c attrs;;
  let remapped kn := List.existsb (fun '(kn', _) => Kernames.eq_kername kn kn') c.(const_remappings_opts) in
  let c := if inline_recursors then merge_attributes_config c [recursor_attributes remapped p] else c in
  let c := if inl.(inline_standard) || inl.(inline_small)
           then merge_attributes_config c [auto_inline_attributes inl remapped p] else c in
  check_wf p;;
  NameSanitize.check_sanitized_injective (NameSanitize.get_sanitizer c)
    (List.app (NameSanitize.PAst_names p) (NameSanitize.config_names c));;
  p <- NameSanitize.sanitize_PAst (NameSanitize.get_sanitizer c) p;;
  c <- NameSanitize.sanitize_config (NameSanitize.get_sanitizer c) c;;
  p <- apply_transforms c lbox p (needs_typed c);;
  check_lowered c p;;
  run_backend c f p.

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

Lemma peregrine_pipeline_parsed c attrs ir io lbox s f p :
  parse_ast s = Ok p ->
  peregrine_pipeline c attrs ir io lbox s f = peregrine_pipeline_ast c attrs ir io lbox p f.
Proof. intros H. unfold peregrine_pipeline. rewrite H. reflexivity. Qed.

Lemma peregrine_pipeline_parse_error c attrs ir io lbox s f e :
  parse_ast s = Err e -> peregrine_pipeline c attrs ir io lbox s f = Err e.
Proof. intros H. unfold peregrine_pipeline. rewrite H. reflexivity. Qed.

(** Main statement: running the tool on the serialization of [p0] is running the
    pipeline on [p0]. *)
Theorem peregrine_pipeline_string_of_PAst c attrs ir io lbox (p0 : PAst) f :
  strings_ok p0 = true ->
  peregrine_pipeline c attrs ir io lbox (Serialize.string_of_PAst p0) f = peregrine_pipeline_ast c attrs ir io lbox p0 f.
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
Theorem peregrine_pipeline_printed (c0 : config') (as0 : list attributes_config) ir io lbox (p0 : PAst) f :
  strings_ok p0 = true -> strings_ok c0 = true -> forallb strings_ok as0 = true ->
  peregrine_pipeline (inl (Serialize.string_of_config c0)) (map Serialize.string_of_attributes_config as0) ir io lbox
    (Serialize.string_of_PAst p0) f =
  peregrine_pipeline_ast (inr c0) (map Serialize.string_of_attributes_config as0) ir io lbox p0 f.
Proof.
  intros Hp Hc Has. rewrite peregrine_pipeline_string_of_PAst by exact Hp.
  unfold peregrine_pipeline_ast. rewrite get_config_string_of_config by exact Hc. reflexivity.
Qed.
