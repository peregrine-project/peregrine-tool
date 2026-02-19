# Cérès [![CircleCI](https://circleci.com/gh/Lysxia/coq-ceres.svg?style=shield)](https://circleci.com/gh/Lysxia/coq-ceres)

Cérès is a Coq library for serialization to S-expressions.

S-expressions
-------------

S-expressions are uniform representations of structured data.

They are an alternative to plain strings as used by `Show` in Haskell and
`Debug` in Rust for example.
S-expressions are more amenable to programmatic consumption, avoiding custom
parsers and enabling flexible formatting strategies.

### Example

This S-expression...

```
(example
  (message "I'm a teapot")
  (code 418))
```

... corresponds to this `sexp` in Coq.

```coq
Definition example : sexp :=
  [ Atom "example"
  ; [ Atom "message" ; Atom (Str "I'm a teapot") ]
  ; [ Atom "code" ; Atom 418%Z ]
  ].
```

### Documentation

The [tutorial module](https://lysxia.github.io/coq-ceres/Tutorial.html) is a good place for a quick start.

[Link to the rendered documentation.](https://lysxia.github.io/coq-ceres/toc.html)

Simplified overview
-------------------

This library offers a type `sexp` with two constructors:

```coq
Inductive sexp :=
| Atom (a : atom)
| List (xs : list sexp)
.
```

Atoms are identifiers (`Raw`), numbers (`Num`) or strings (`Str`).

```coq
Variant atom : Set :=
| Num (n : Z)       (* Integers. *)
| Str (s : string)  (* Literal strings. *)
| Raw (s : string)  (* Simple atoms (e.g., ADT tags). *)
                    (* Should fit in this alphabet: [A-Za-z0-9'=+*/:!?@#$%^&<>.,|_~-]. *)
.
```

Two classes `Serialize` and `Deserialize` are provided to define canonical
serializers and deserializers between your types and S-expressions.
The following functions are provided for conversions to `sexp` or directly to
`string`:

```coq
Definition to_sexp {A} `{Serialize A} : A -> sexp.
Definition from_sexp {A} `{Deserialize A} : sexp -> error + A.

Definition to_string {A} `{Serialize A} : A -> string.
Definition from_string {A} `{Deserialize A} : string -> error + A.
```

Usage
-----

Import the main module of the library.

```coq
Require Import Ceres.Ceres.
```

This exports:

- `CeresS`: the core definitions for S-expressions.
- `CeresSerialize`: the `Serialize` type class (`sexp -> error + mytype`).
- `CeresDeserialize`: the `Deserialize` type class (`mytype -> sexp`).
- `CeresRoundtrip`: roundtrip properties for serializers and deserializers.
- `CeresFormat`: format S-expressions as strings (`sexp -> string`).
- `CeresParser`: S-expression parser (`string -> error + sexp`).

Other modules in the library:

- `CeresParserUtils`: low-level primitives for the S-expression parser
- `CeresParserRoundtrip`, `CeresParserRoundtripProof`:
  Correctness proof of the parser. Currently, only soundness is proved
  (i.e., parse-then-print roundtrip).

Internals:

- `CeresUtils`: miscellaneous.
- `CeresParserInternal`: S-expression parser, internals
- `CeresString`: general string utilities.

Core definitions
----------------

The type of S-expressions is actually parameterized by the type of atoms.

```coq
Inductive sexp_ (A : Type) :=
| Atom_ (a : A)
| List (xs : list (sexp_ A))
.
```

By default, it is specialized to the `atom` type, so that the main S-expression type is
`sexp := sexp_ atom`.

```coq
Notation sexp := (sexp_ atom).
Notation Atom := (@Atom_ atom).

Coercion Num : Z >-> atom.
Coercion Raw : string >-> atom.

(* Destructors *)
Definition get_Num : atom -> option Z.
Definition get_Str : atom -> option string.
Definition get_Raw : atom -> option string.
```

Serialization
-------------

Serializers can be defined as instances of the `Serialize` type class.

```coq
Class Serialize (A : Type) : Type :=
  to_sexp : A -> sexp.
```

S-expressions can be serialized to a `string`. Thus, so can serializable types.

```coq
Definition to_string {A : Type} `{Serialize A} : A -> string.
```

For numeric types, it is sufficient to define a conversion to `Z` as an
instance of `Integral`.

```coq
Class Integral (A : Type) : Type :=
  to_Z : A -> Z.

Instance Serialize_Integral (A : Type) : Integral A -> Serialize A.
```

Deserialization
---------------

Going the other way requires some additional error handling.

```coq
Class Deserialize (A : Type) : Type := ...

Definition from_sexp {A} `{Deserialize A} : sexp -> error + A.
Definition from_string {A} `{Deserialize A} : string -> error + A.
```

Again, a simplified interface for numeric types is thus provided,
with a `SemiIntegral` class.

```coq
Class SemiIntegral (A : Type) : Type :=
  from_Z : Z -> option A.

Instance Deserialize_SemiIntegral (A : Type) : SemiIntegral A -> Deserialize A.
```

Roundtrip properties
--------------------

The module `CeresRoundtrip` defines some roundtripping properties
and lemmas to help prove them.

```coq
Class CompleteClass {A} `{Serialize A} `{Deserialize A} : Prop.
Class SoundClass {A} `{Serialize A} `{Deserialize A} : Prop.
```

Generic encoding
----------------

There are no strong requirements on the encodings implemented by `Serialize`
and `Deserialize` instances, but some utilities are provided for the following
default encoding for inductive types:

- Nullary constructors are atoms `con`.
- Non-nullary constructors are lists `(con x y z)`.

Serialization is straightforward by pattern-matching.

For deserialization, the module `CeresDeserialize.Deser` provides
some utilities.

### Standard types

- `unit`, `bool`, `sum` and `option` follow that standard encoding.
- `(x, y) : prod A B` is encoded as `(X Y)` where `X` and `Y` are the encodings of `x` and `y`.
- `[x; y; z] : list A` is encoded as `(X Y Z)`.
- `"somestring" : string` is encoded as `"somestring"`.
- `"c" : ascii` is encoded as `"c"`.
- `33 : Z` (or `N`, `nat`) is encoded as `33`.

### Recursive types

Recursive serializers and deserializers can be defined using explicit fixpoints.

For deserializers, that means to bind the expression explicitly, since that's
the decreasing argument, but immediately pass it as the last argument of
`Deser.match_con`:

```coq
Definition Deserialize_unary : Deserialize nat :=
  fix deser_nat (l : loc) (e : sexp) {struct e} :=
    Deser.match_con "nat"
      [ ("Z", 0%nat) ]
      [ ("S", Deser.con1 S deser_nat) ] l e.
```

Developer notes
---------------

### Build the documentation

Extra directories:

- `coqdocjs`: a clone of [coqdocjs](https://github.com/coq-community/coqdocjs)
- `doc`: a clone of this repo's `gh-pages` branch

```
make html && rm -r doc/docs && mv html doc/docs
cd doc
git add docs && git commit -m "Update" && git push
```

See also
--------

- Real World OCaml, [Chapter 17, Data Serialization with
  S-expressions](https://v1.realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html).
- [Down with Show!](https://harry.garrood.me/blog/down-with-show-part-3/), a
  blog post by Harry Garrood advocating for using structured representations
  instead of strings.
