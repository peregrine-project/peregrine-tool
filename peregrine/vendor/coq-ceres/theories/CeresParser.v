From Stdlib Require Import NArith (* String *).
From MetaRocq.Utils Require Import bytestring.

From Ceres Require Import
  CeresS
  CeresParserUtils
  CeresParserInternal.

(** Parse a string into a list of S-expressions. *)
Definition parse_sexps (s : string) : error + list sexp :=
  match parse_sexps_ initial_state 0%N s with
  | (None, p, i) => eof i p
  | (Some e, _, _) => inl e
  end.

(** Parse a string into one S-expression. Subsequent expressions, if any, are ignored. *)
Definition parse_sexp (s : string) : error + sexp :=
  let '(e, p, i) := parse_sexps_ initial_state 0%N s in
  match List.rev' (parser_done i), e with
  | (r :: _)%list, _ => inr r
  | nil, Some e => inl e
  | nil, None =>
    match eof i p with
    | inl e => inl e
    | inr (r :: _)%list => inr r
    | inr nil => inl EmptyInput
    end
  end.
