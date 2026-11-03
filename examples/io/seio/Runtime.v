(** The IO operations of SEIO* (andricicezar/fstar-io, [seiostar/lambdabox]),
    with their names and types, so that SEIO*'s realizations of them serve
    Rocq programs too.  A file descriptor is a [nat]; [inl] is success and
    [inr tt] failure.  The module must be called [Runtime]: Peregrine names
    the axiom [io_read] of this file [Runtime.io_read], which the OCaml
    backend refers to as [Axioms.def_Runtime_io_read]. *)
From Stdlib Require Import PrimString.

Axiom io_read : nat -> string + unit.
Axiom io_write : nat * string -> unit + unit.
Axiom io_open : string -> nat + unit.
Axiom io_close : nat -> unit + unit.
