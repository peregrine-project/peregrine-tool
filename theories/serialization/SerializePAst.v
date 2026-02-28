From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import PAst.
From Peregrine Require Import SerializeEAst.
From Peregrine Require Import SerializeExAst.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

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



Definition string_of_typed_env (env : typed_env) : string :=
  @to_string typed_env Serialize_typed_env env.

Definition string_of_untyped_env (env : untyped_env) : string :=
  @to_string untyped_env Serialize_untyped_env env.

Definition string_of_PAst (ast : PAst) : string :=
  @to_string PAst Serialize_PAst ast.
