(** * Serialization to S-expressions *)

(* begin hide *)
From Stdlib Require Import
  List
  ZArith
  Strings.Byte
(*   Ascii
  String *).
From MetaRocq.Utils Require Import bytestring.

From Ceres Require Import
  CeresS
  CeresFormat
  CeresString.
(* end hide *)

(** Serialization to S-expressions. *)
Class Serialize (A : Type) :=
  to_sexp : A -> sexp.

(** Serialize a value to a string. *)
Definition to_string {A} `{Serialize A} : A -> string :=
  fun a => string_of_sexp (to_sexp a).

(** ** Serialize integers *)

(** Integer representations. *)
Class Integral (A : Type) :=
  to_Z : A -> Z.

(** Integers are serializable. *)
Global
Instance Serialize_Integral {A : Type} `(Integral A) : Serialize A :=
  fun z => Atom (to_Z z).

Global
Instance Integral_nat : Integral nat := Z.of_nat.
Global
Instance Integral_N : Integral N := Z.of_N.
Global
Instance Integral_Z : Integral Z := id.

(** ** Serialize common types *)

Global
Instance Serialize_bool : Serialize bool
  := fun b => Atom (string_of_bool b).

Global
Instance Serialize_option {A} `(Serialize A) : Serialize (option A)
  := fun oa =>
    match oa with
    | None => Atom "None"%bs
    | Some a => [ Atom "Some"%bs ; to_sexp a ]%sexp
    end.

Global
Instance Serialize_sum {A B} `(Serialize A) `(Serialize B)
  : Serialize (A + B)
  := fun ab =>
    match ab with
    | inl a => [ Atom "inl"%bs ; to_sexp a ]%sexp
    | inr b => [ Atom "inr"%bs ; to_sexp b ]%sexp
    end.

Global
Instance Serialize_product {A B} `(Serialize A) `(Serialize B)
  : Serialize (A * B)
  := fun ab => [ to_sexp (fst ab) ; to_sexp (snd ab) ]%sexp.

Global
Instance Serialize_Empty_set : Serialize Empty_set
  := fun v => match v with end.

Global
Instance Serialize_unit : Serialize unit
  := fun _ => Atom "tt"%bs.

Global
Instance Serialize_byte : Serialize byte
  := fun a => Atom (Str (String.String a ""%bs)).

Global
Instance Serialize_string : Serialize string
  := fun s => Atom (Str s).

Global
Instance Serialize_list {A} `{Serialize A} : Serialize (list A)
  := fun xs => List (List.map to_sexp xs).

Global
Instance Serialize_sexp : Serialize sexp := id.
