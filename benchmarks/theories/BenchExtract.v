(** * Benchmark Extraction

    Creates benchmark entry points with fixed inputs.

    Input size tiers:
    - small: Quick tests (~1 second)
    - medium: Meaningful comparison (~10-60 seconds)
    - large: Stress test (~minutes, optional)

    Official Benchmarks Game sizes (N=21, N=12, N=10000) are impractical
    for our purely functional, single-threaded implementation.
*)

From Stdlib Require Import ZArith List String.
From BenchmarksGame Require Import Common BinaryTrees Fannkuch Pidigits.
From Peregrine Require Import Loader.

(** =========================================== *)
(** Binary Trees: O(2^n) complexity             *)
(** Official: N=21 (impractical)                *)
(** =========================================== *)

(* Small: ~instant *)
Definition binary_trees_10 : Z := binary_trees_simple 10.
(* Medium: measurable *)
Definition binary_trees_14 : Z := binary_trees_simple 14.
(* Large: stress test *)
Definition binary_trees_16 : Z := binary_trees_simple 16.

Peregrine Extract "binary_trees_10.ast" binary_trees_10.
Peregrine Extract "binary_trees_14.ast" binary_trees_14.
Peregrine Extract "binary_trees_16.ast" binary_trees_16.

(** =========================================== *)
(** Fannkuch Redux: O(n!) complexity            *)
(** Official: N=12 (impractical for pure FP)    *)
(** =========================================== *)

(* Small: 5040 permutations *)
Definition fannkuch_7 : nat := fannkuch_simple 7.
(* Medium: 40320 permutations *)
Definition fannkuch_8 : nat := fannkuch_simple 8.
(* Large: 362880 permutations *)
Definition fannkuch_9 : nat := fannkuch_simple 9.

Peregrine Extract "fannkuch_7.ast" fannkuch_7.
Peregrine Extract "fannkuch_8.ast" fannkuch_8.
Peregrine Extract "fannkuch_9.ast" fannkuch_9.

(** =========================================== *)
(** Pidigits: O(n^2) complexity                 *)
(** Official: N=10000 (may be feasible)         *)
(** =========================================== *)

(* Small: quick test *)
Definition pidigits_27 : Z := pidigits_number 27.
(* Medium: reasonable test *)
Definition pidigits_100 : Z := pidigits_number 100.
(* Large: longer test *)
Definition pidigits_500 : Z := pidigits_number 500.

Peregrine Extract "pidigits_27.ast" pidigits_27.
Peregrine Extract "pidigits_100.ast" pidigits_100.
Peregrine Extract "pidigits_500.ast" pidigits_500.
