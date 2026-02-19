(** * Parser specification *)

(** This is the specification of the parser, turning byte strings into S-expressions. *)

(** Main relations:
  - [token_string]: relating strings to streams of tokens;
  - [sexp_tokens]: relating tokens to S-expressions.

  The soundness theorem ("parse then print") is stated below, [PARSE_SEXPS_SOUND].
  The completeness theorem ("print then parse") is TODO.

  These are justs the theorem statements, ensuring that they don't
  depend on any proof details. The proofs are in [CeresParserRoundtripProof].
 *)

From Stdlib Require Import
(*   Ascii
  String *)
  List
  ZArith
  DecimalString.
From MetaRocq.Utils Require Import bytestring.
From Ceres Require Import
  CeresS
  CeresString
  CeresParserUtils
  CeresParser.

Import ListNotations.

Module Token.

Inductive t : Type :=
| Open : t
| Close : t
| Atom (s : string) : t
| Str (s : string) : t
.

End Token.

Local Open Scope bs_scope.
Local Open Scope list_scope.


(* * Lexer *)

(* Here we specify how to convert strings of bytes to streams of tokens. *)

(* [whitespaces s] holds when [s] consists of only whitespace,
   as defined by [is_whitespace]. *)
Definition whitespaces (s : string) : Prop :=
  string_forall is_whitespace s = true.

(* [comment s] holds when [s] is a comment: starts with
   a semicolon [';'], ends with a newline ['\n']. *)
Inductive comment : string -> Prop :=
| comment_mk s : comment (";" :: s ++ newline)%bs.

(* [atom_string s] holds when [s] is an atom. *)
Definition atom_string (s : string) : Prop :=
  s <> ""%bs /\ string_forall is_atom_char s = true.

(* [after_atom_string false s] if the non-empty string [s] may appear right
   after an atom. This predicate is used to avoid ambiguity: two atoms
   cannot follow each other immediately, they must at least be separated
   by a space, so [ab] is unambiguously one atom, not two separate atoms [a]
   and [b].  *)
Inductive after_atom_string : bool -> string -> Prop :=
| after_atom_nil : after_atom_string true ""%bs
| after_atom_cons c s more : is_atom_char c = false -> after_atom_string more (c :: s)%bs.
Global Hint Constructors after_atom_string : ceres.

Lemma after_atom_string_nil_inv more : after_atom_string more ""%bs -> more = true.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma after_atom_string_cons more c s : is_atom_char c = false -> after_atom_string more (c :: s)%bs.
Proof.
  destruct more; auto with ceres.
Qed.

(* [string_string s0 s1] if the string [s1] encodes the raw string [s0]
   (i.e., [s1] contains the bytes you would find in a file).
 *)
Definition string_string (s0 : string) (s1 : string) : Prop :=
  s1 = ("""" :: _escape_string "" s0 ++ """")%bs.

(* Lexer relation: [token_string more ts s] if the string [s] can be split into tokens [ts].
   - Handling of spaces and comments.
   - Corner cases for spaces around atoms (["ab"] should not be parsed as ["a"] then ["b"]).
   - [more] is [true] if the last token is an [Token.Atom] and there are no more
     characters after it, in which case we need to be careful when appending something.
 *)
Inductive token_string (more : bool) : list Token.t -> string -> Prop :=
| token_string_nil : token_string more [] ""
| token_string_open ts s
  : token_string more ts s -> token_string more (Token.Open :: ts) ("(" :: s)%bs
| token_string_close ts s
  : token_string more ts s -> token_string more (Token.Close :: ts) (")" :: s)%bs
| token_string_atom ts s1 s
  : atom_string s1 -> after_atom_string more s ->
    token_string more ts s -> token_string more (Token.Atom s1 :: ts) (s1 ++ s)%bs
| token_string_string ts s0 s1 s
  : string_string s0 s1 -> token_string more ts s -> token_string more (Token.Str s0 :: ts) (s1 ++ s)%bs
| token_string_spaces ts ws s
  : whitespaces ws -> token_string more ts s -> token_string more ts (ws ++ s)%bs
| token_string_comment ts c s
  : comment c -> token_string more ts s -> token_string more ts (c ++ s)%bs.
Global Hint Constructors token_string : ceres.

Inductive more_ok : bool -> string -> Prop :=
| more_ok_false s : more_ok false s
| more_ok_true c s : is_atom_char c = false -> more_ok true (c :: s)%bs
.
Global Hint Constructors more_ok : ceres.

Lemma more_ok_nil_inv more : more_ok more "" -> more = false.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma more_ok_cons more c s : is_atom_char c = false -> more_ok more (c :: s)%bs.
Proof.
  destruct more; auto with ceres.
Qed.

(* * Parser *)

(* Here we specify how to turn tokens into trees, S-expressions. *)

(* Lift parser relation on single elements [A] to a parser relation on lists
   of elements [list A].
   Remark: This is like the monadic bind on lists, but using relations instead of functions. *)
Inductive list_tokens {A B} (tks : A -> list B -> Prop) : list A -> list B -> Prop :=
| list_tokens_nil : list_tokens tks [] []
| list_tokens_cons x xs y ys
  : tks x y -> list_tokens tks xs ys -> list_tokens tks (x :: xs) (y ++ ys)
.
Global Hint Constructors list_tokens : ceres.

(* Parser relation on atoms. Each atom is a single token. *)
Inductive atom_token : atom -> Token.t -> Prop :=
| atom_token_Raw s : atom_token (Raw s) (Token.Atom s)
| atom_token_Num s z
  : NilZero.int_of_string (String.to_string s) = Some z ->
    atom_token (Num (Z.of_int z)) (Token.Atom s)
| atom_token_Str s : atom_token (Str s) (Token.Str s).
Global Hint Constructors atom_token : ceres.

(* Parser relation on S-expressions. This is the main definition of this file. *)
Inductive sexp_tokens : sexp -> list Token.t -> Prop :=
| sexp_tokens_Atom a t : atom_token a t -> sexp_tokens (Atom_ a) [t]
| sexp_tokens_List es ts
  : list_tokens sexp_tokens es ts ->
    sexp_tokens (List es) (Token.Open :: ts ++ [Token.Close])
.
Global Hint Constructors sexp_tokens : ceres.

(* Parser relation on lists of S-expressions (without the outer parentheses). *)
Notation list_sexp_tokens := (list_tokens sexp_tokens).

(** [on_right] is a helper to phrase conditional propositions of the form
  "if this parser succeeds, then ...".

  Concretely, this predicate transformer lifts a predicate on the right
  component of a sum.  It is [True] for [inl] elements. *)
Definition on_right {A B} (x : A + B) (P : B -> Prop) : Prop :=
  match x with
  | inl _ => True
  | inr b => P b
  end.

(** Soundness: if the parser succeeds, then the expressions relate to the input string.
  ("Parse then print" roundtrip.) I call this "soundness" because it means that the
  parser rejects garbage.
 *)
Definition PARSE_SEXPS_SOUND : Prop :=
  forall (s : string) (es : list sexp),
    on_right (parse_sexps s) (fun es =>
      exists ts, list_sexp_tokens es ts /\ token_string false ts (s ++ newline))%bs.

(* TODO: Completeness *)
