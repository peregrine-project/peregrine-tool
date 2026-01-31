(** * Typed Extraction for Rust Backend

    Creates typed benchmark entry points (.tast files)
    for compilation to Rust (native and WASM targets).
*)

From Stdlib Require Import ZArith List String.
From BenchmarksGame Require Import Common BinaryTrees Fannkuch Pidigits.
From Peregrine Require Import Loader.

(** =========================================== *)
(** Binary Trees                                *)
(** =========================================== *)

Definition binary_trees_10 : Z := binary_trees_simple 10.
Definition binary_trees_14 : Z := binary_trees_simple 14.

Peregrine Extract Typed "binary_trees_10.tast" binary_trees_10.
Peregrine Extract Typed "binary_trees_14.tast" binary_trees_14.

(** =========================================== *)
(** Fannkuch Redux                              *)
(** =========================================== *)

Definition fannkuch_7 : nat := fannkuch_simple 7.
Definition fannkuch_8 : nat := fannkuch_simple 8.

Peregrine Extract Typed "fannkuch_7.tast" fannkuch_7.
Peregrine Extract Typed "fannkuch_8.tast" fannkuch_8.

(** =========================================== *)
(** Pidigits                                    *)
(** =========================================== *)

Definition pidigits_27 : Z := pidigits_number 27.
Definition pidigits_100 : Z := pidigits_number 100.

Peregrine Extract Typed "pidigits_27.tast" pidigits_27.
Peregrine Extract Typed "pidigits_100.tast" pidigits_100.
