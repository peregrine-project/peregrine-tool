From Stdlib Require Import String.
From MetaRocq.Template Require ExtractableLoader.

Declare ML Module "rocq_verified_extraction.plugin".
Declare ML Module "rocq-verified-extraction-malfunction.plugin".

(** This is required for linking with the OCaml FFIs which assume
    the ocaml ordering on [bool] values. *)
Verified Extract Inductives [ bool => "bool" [ 1 0 ] ].
