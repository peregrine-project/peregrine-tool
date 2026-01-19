From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import PAst.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import SerializeExAst.
From Stdlib Require Import List.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Serializers *)

Instance Serialize_typed_env : Serialize typed_env :=
 fun p =>
    to_sexp p.

Instance Serialize_untyped_env : Serialize untyped_env :=
 fun p =>
    to_sexp p.

Instance Serialize_PAst : Serialize PAst :=
  fun ast =>
    match ast with
    | Untyped env t => [ Atom "Untyped"; to_sexp env; to_sexp t ]
    | Typed env t => [ Atom "Typed"; to_sexp env; to_sexp t ]
    end%sexp.



(** * Deserializers *)

Instance Deserialize_typed_env : Deserialize typed_env :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_untyped_env : Deserialize untyped_env :=
 fun l e =>
    _from_sexp l e.

Instance Deserialize_PAst : Deserialize PAst :=
  fun l e =>
    Deser.match_con "PAst"
      []
      [ ("Untyped", Deser.con2_ Untyped)
      ; ("Typed", Deser.con2_ Typed)
      ]
      l e.


Definition string_of_PAst (ast : PAst) : string :=
  @to_string PAst Serialize_PAst ast.

Definition PAst_of_string (s : string) : error + PAst :=
  @from_string PAst Deserialize_PAst s.
