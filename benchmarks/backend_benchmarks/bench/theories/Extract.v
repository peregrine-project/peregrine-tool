(** * Extraction of Benchmarks Game to various backends *)

From Stdlib Require Import ZArith List String.
From BenchmarksGame Require Import Common BinaryTrees Fannkuch Pidigits.

From Peregrine Require Import Loader.

(** ===================== *)
(** Binary Trees Benchmark *)
(** ===================== *)

(** Extract binary_trees_simple to file *)
Peregrine Extract "binary_trees.ast" binary_trees_simple.

(** ===================== *)
(** Fannkuch Benchmark *)
(** ===================== *)

(** Extract fannkuch_simple to file *)
Peregrine Extract "fannkuch.ast" fannkuch_simple.

(** ===================== *)
(** Pidigits Benchmark *)
(** ===================== *)

(** Extract pidigits_number to file *)
Peregrine Extract "pidigits.ast" pidigits_number.

(** ===================== *)
(** Combined test function *)
(** ===================== *)

(** Run all benchmarks with small inputs and sum results *)
Definition run_all_benchmarks : Z :=
  let bt := binary_trees_simple 6 in      (* Binary trees with depth 6 *)
  let fk := Z.of_nat (fannkuch_simple 5) in (* Fannkuch with n=5 *)
  let pi := pidigits_number 5 in          (* First 5 digits of pi *)
  (bt + fk + pi)%Z.

Peregrine Extract "run_all.ast" run_all_benchmarks.
