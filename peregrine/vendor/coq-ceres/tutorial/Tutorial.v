(** * Ceres library tutorial *)

(** {{https://github.com/Lysxia/coq-ceres/tree/master/tutorial/Tutorial.v} Source of this file} *)

From Stdlib Require Import List ZArith (* String *).
From MetaRocq.Utils Require Import bytestring.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.

(** ** Introduction *)

(** Ceres is a library for serializing Coq data types,
so they can be stored or displayed outside of Coq's interactive
environment (for example, in an extracted program).

Ceres manipulates S-expressions ("LISP notation"), a generic format with:

- a common human-readable string representation,
- a tree structure which makes it easy to map to user-defined Coq types.

Thus the library consists of two components mediating between these
data representations:

<<
        Strings
              ↕ (1) Parser/printer
  S-expressions
              ↕ (2) Serialization
Your data types
>>
*)

(** ** S-expressions *)

(** *** Types and constructors *)

(** S-expressions have type [sexp], with two constructors, [Atom] and [List].
So S-expressions are trees of atoms.
*)

Check (sexp : Type).

Check (Atom : atom -> sexp).
Check (List : list sexp -> sexp).

(** Note: The actual definition of [sexp] is a little fancier than a plain
inductive type, but don't pay too much attention to that. *)

(** Here is an example of an S-expression in its concrete syntax:

<<
(example
  (message "I'm a teapot")
  (code 418))
>>
*)

(** Atoms are numbers ([Num]), strings ([Str]), and "raw identifiers" ([Raw]). *)

(** Numbers are integers (they may be negative). *)
Check (Num : Z -> atom).

(** Strings are arbitrary values of type [string].
Their concrete syntax is between double quotes, possibly containing escape sequences
(e.g., <<"\\">>, <<"\n">>, <<"\010">>).

Use strings to embed actual strings from your data types, or to embed other
arbitrary syntax (e.g., dates, fractional numbers, hex, binary). *)
Check (Str : string -> atom).

(** Raw identifiers correspond to unquoted strings in the concrete syntax of S-expressions.
Raw identifiers also have type [string], but they must consist only of
characters in the set <<[A-Za-z0-9'=+*/:!?@#$%^&<>.,|_~-]>>.

For the purpose of encoding Coq inductive types, their constructor names
can be encoded as [Raw] atoms. *)
Check (Raw : string -> atom).

(** Note: [Raw] is a coercion, but [Str] is not (that would be ambiguous otherwise).
Thus a [string] can be put anywhere an [atom] is expected. *)

Check (Raw "example" = "example")%bs.

(** *** Examples *)

Definition example1 : sexp :=
  List [ Atom (Raw "example")
       ; List [ Atom (Raw "message") ; Atom (Str "I'm a teapot") ]
       ; List [ Atom (Raw "code") ; Atom 418%Z ]
       ].

(** The list notation is also overloaded to implicitly add the [List] constructor:
[[
Notation "[ ]" := (List nil) : sexp_scope.
Notation "[ x ]" := (List (@cons (sexp_ _) x nil)) : sexp_scope.
Notation "[ x ; y ; .. ; z ]"
  := (List (@cons (sexp_ _) x (@cons (sexp_ _) y .. (@cons (sexp_ _) z nil) .. )))
  : sexp_scope.
]]

Remember to open [sexp_scope]:
- with the command <<Local Open Scope sexp_scope.>>
- or with the key <<%sexp>>.

Also open [string_scope] to benefit from the [Raw] coercion.
*)

Definition example2 : sexp :=
  [ Atom "example"
  ; [ Atom "message" ; Atom (Str "I'm a teapot") ]
  ; [ Atom "code" ; Atom 418%Z ]
  ]%sexp.

(** ** String conversions *)

Check (parse_sexp : string -> CeresParserUtils.error + sexp).
Check (parse_sexps : string -> CeresParserUtils.error + list sexp).
Check (string_of_sexp : sexp -> string).

(** The function [parse_sexp] (resp. [parse_sexps]) reads a [string] intro
a single [sexp] (resp. a list of [sexp]). An error is returned if the string
is not well-formed. *)

(** The function [string_of_sexp] converts a [sexp] into a [string]. *)

(** ** Serialization of data types *)

(** Example inductive type: *)
Inductive t : Set :=
| Number : nat -> t
| Bool : bool -> t
| If : t -> t -> t -> t
| Plus : t -> t -> t
.

(** We define a [Serialize] and [Deserialize] instance to convert it to and
from S-expressions. *)

(** *** Serialize *)

(** An instance [Serialize t] is a function [t -> sexp]. *)
Check (eq_refl : Serialize t = (t -> sexp)).

(** Since [t] is recursive, this function will be defined using [fix]. *)

Global
Instance Serialize_t : Serialize t :=
  fix sz (a : t) : sexp :=
    match a with
    | Number n => [ Atom "Number" ; to_sexp n ]
    | Bool b => [ Atom "Bool" ; to_sexp b ]
    | If x y z => [ Atom "If" ; sz x ; sz y ; sz z ]
    | Plus x y => [ Atom "Plus" ; sz x ; sz y ]
    end%sexp.

(** Having defined a [Serialize] instance, the [to_sexp] function becomes available
for that type: *)
Check (to_sexp : t -> sexp).

(** A [Serialize] instance can be any function [t -> sexp], but for uniformity,
and to benefit from library combinators for deserialization, it is recommended
to stick to the following encoding.

A constructor [C x y z] as a list <<(C x y z)>>, i.e.,
[List [ Atom "C" ; to_sexp x ; to_sexp y ; to_sexp z ]] in Gallina,
such that the first element is the name of the constructor as an atom, and the
subsequent elements are the fields of the constructor.
*)


(** *** Deserialize *)

(** For deserialization, the helper [Deser.match_con] quickly provides
an implementation to decode the encoding described above. *)

(** An instance [Deserialize t] is a function [loc -> sexp -> error + t]. *)
Check (eq_refl : Deserialize t = (loc -> sexp -> error + t)).

(** The fact that these are functions is mostly hidden by the helpers, except
for recursive types where you have to build a fixpoint and explicitly pass the
two arguments to [Deser.match_con]. *)

Global
Instance Deserialize_t : Deserialize t :=
  fix ds (l : loc) (e : sexp) : error + t :=
    Deser.match_con "t" []
      [ ("Number", Deser.con1_ Number)
      ; ("Bool", Deser.con1_ Bool)
      ; ("If", Deser.con3 If ds ds ds)
      ; ("Plus", Deser.con2 Plus ds ds)
      ] l e.

(** Having defined a [Deserialize] instance, the [from_sexp] function becomes available
for that type: *)
Check (from_sexp : sexp -> error + t).

(** To explain [Deser.match_con] in more details, it takes three main arguments:
- the name of the type, as a string, for error messages
- a list of cases for nullary constructors of [t] paired with their names ([list (string * t)])
- a list of cases for non-nullary constructors, also with their names,
  wrapped using one of the following combinators depending on its arity:
  [Deser.con1], [Deser.con2], [Deser.con3], etc.

The functions [Deser.con1], etc., take the constructor plus one more argument
per field, which is a deserializer for that field.

- Use the [_from_sexp] deserializer for fields whose type is already an instance of [Deserialize];
  the variants [Deser.con1_], [Deser.con2_], etc., suffixed by an underscore,
  can be used to supply [_from_sexp] to all fields.
- Use the fixpoint for recursive fields.
 *)
