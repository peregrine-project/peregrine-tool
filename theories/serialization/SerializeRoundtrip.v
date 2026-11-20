(** * String-level round trip for peregrine's input formats

    Ceres's [CeresRoundtrip] only relates [to_sexp] and [_from_sexp] (sexp level).
    Combined with completeness of the Ceres parser ([CeresParserComplete]) and
    the fact that all [Raw] atoms produced by peregrine's serializers are
    parseable ([SerializeRawOk], [SerializeConfigRawOk]) we obtain the string level
    statements: [from_string (to_string a) = inr a], provided every string atom of
    [to_sexp a] only contains bytes that the printer does not escape as [\ddd]
    (TAB, LF, CR, 32-126, 128-244). *)

From Stdlib Require Import List Bool.
From MetaRocq.Utils Require Import bytestring.
From CeresBS Require Import Ceres CeresString CeresParser CeresRoundtrip.
From Peregrine Require Import PAst Config ConfigUtils.
From Peregrine Require Import CeresParserComplete SerializeRawOk SerializeConfigRawOk.
From Peregrine Require Import Serialize Deserialize SerializePAst DeserializePAst
  SerializeConfig DeserializeConfig SerializeComplete SerializeSound.

Local Open Scope bs_scope.

(** All string atoms of the serialization of [a] are printable without [\ddd] escapes. *)
Definition strings_ok {A} `{Serialize A} (a : A) : bool :=
  sexp_forall_atoms atom_str_okb (to_sexp a).

(** ** Generic statements *)

Section Generic.
  Context {A : Type} `{Serialize A} `{Deserialize A}.

  (** Completeness: parsing the printed value gives it back. *)
  Theorem from_string_to_string `{!CompleteClass A} `{!RawOk A} (a : A) :
    strings_ok a = true -> from_string (to_string a) = inr a.
  Proof.
    intros Hs. unfold from_string, to_string.
    rewrite parse_sexp_string_of_sexp'.
    - apply complete_class.
    - unfold sexp_okb. rewrite sexp_okb_split, raw_ok_to_sexp. exact Hs.
  Qed.

  (** Same, allowing trailing whitespace (e.g. a final newline in the file). *)
  Theorem from_string_to_string_ws `{!CompleteClass A} `{!RawOk A} (a : A) ws :
    strings_ok a = true -> string_forall is_whitespace ws = true ->
    from_string (to_string a ++ ws) = inr a.
  Proof.
    intros Hs Hws. unfold from_string, to_string.
    rewrite parse_sexp_string_of_sexp by
      (try exact Hws; unfold sexp_okb; rewrite sexp_okb_split, raw_ok_to_sexp; exact Hs).
    apply complete_class.
  Qed.

  (** Soundness: if a string parses to [a], its s-expression is the serialization of [a]. *)
  Theorem from_string_sound `{!SoundClass A} (s : string) (a : A) :
    from_string s = inr a -> parse_sexp s = inr (to_sexp a).
  Proof.
    unfold from_string. destruct (parse_sexp s) as [e|e]; [discriminate|].
    intros Hd. f_equal. symmetry. eapply sound_class. exact Hd.
  Qed.

  (** Determinism / uniqueness: the only value read from a printed [a0] is [a0]. *)
  Corollary from_string_to_string_inv `{!CompleteClass A} `{!RawOk A} (a0 a : A) :
    strings_ok a0 = true -> from_string (to_string a0) = inr a -> a = a0.
  Proof.
    intros Hs Hp. rewrite from_string_to_string in Hp by exact Hs. congruence.
  Qed.

  (** Any two strings that parse to the same value have the same s-expression,
      which is the one of the value. *)
  Corollary from_string_same_sexp `{!SoundClass A} `{!CompleteClass A} `{!RawOk A}
    (s : string) (a : A) :
    from_string s = inr a -> strings_ok a = true ->
    parse_sexp s = parse_sexp (to_string a).
  Proof.
    intros Hp Hs. rewrite (from_string_sound s a Hp).
    unfold to_string. symmetry. apply parse_sexp_string_of_sexp'.
    unfold sexp_okb. rewrite sexp_okb_split, raw_ok_to_sexp. exact Hs.
  Qed.
End Generic.

(** ** Instances for peregrine's input formats *)

Theorem PAst_of_string_complete (p : PAst) :
  strings_ok p = true -> Deserialize.PAst_of_string (Serialize.string_of_PAst p) = inr p.
Proof. apply from_string_to_string. Qed.

Theorem PAst_of_string_complete_ws (p : PAst) ws :
  strings_ok p = true -> string_forall is_whitespace ws = true ->
  Deserialize.PAst_of_string (Serialize.string_of_PAst p ++ ws) = inr p.
Proof. apply from_string_to_string_ws. Qed.

Theorem PAst_of_string_sound (s : string) (p : PAst) :
  Deserialize.PAst_of_string s = inr p -> parse_sexp s = inr (to_sexp p).
Proof. apply from_string_sound. Qed.

Theorem config_of_string_complete (c : config') :
  strings_ok c = true -> Deserialize.config_of_string (Serialize.string_of_config c) = inr c.
Proof. apply from_string_to_string. Qed.

Theorem config_of_string_sound (s : string) (c : config') :
  Deserialize.config_of_string s = inr c -> parse_sexp s = inr (to_sexp c).
Proof. apply from_string_sound. Qed.

Theorem attributes_config_of_string_complete (a : attributes_config) :
  strings_ok a = true -> Deserialize.attributes_config_of_string (Serialize.string_of_attributes_config a) = inr a.
Proof. apply from_string_to_string. Qed.

Theorem attributes_config_of_string_sound (s : string) (a : attributes_config) :
  Deserialize.attributes_config_of_string s = inr a -> parse_sexp s = inr (to_sexp a).
Proof. apply from_string_sound. Qed.
