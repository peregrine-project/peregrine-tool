From Stdlib Require Import String.
From MetaRocq.Template Require ExtractableLoader.
From Malfunction Require Export PrintMli.

Declare ML Module "rocq_verified_extraction.plugin".
Declare ML Module "rocq-verified-extraction-ocaml.plugin".

(** This is required for linking with the OCaml FFIs which assume
    the ocaml ordering on [bool] values. *)
Verified Extract Inductives [ bool => "bool" [ 1 0 ] ].