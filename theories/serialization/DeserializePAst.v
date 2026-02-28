From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import PAst.
From Peregrine Require Import DeserializeEAst.
From Peregrine Require Import DeserializeExAst.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



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
      [ ("Untyped", con2_ Untyped)
      ; ("Typed", con2_ Typed)
      ]
      l e.



Definition typed_env_of_string (s : string) : error + typed_env :=
  @from_string typed_env Deserialize_typed_env s.

Definition untyped_env_of_string (s : string) : error + untyped_env :=
  @from_string untyped_env Deserialize_untyped_env s.

Definition PAst_of_string (s : string) : error + PAst :=
  @from_string PAst Deserialize_PAst s.
