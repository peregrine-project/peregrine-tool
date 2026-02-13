(** * Extraction for New Benchmarks *)

From Stdlib Require Import ZArith Uint63.
From Peregrine Require Import Loader.
From BenchmarksGame Require Import NQueens Ackermann Tak Quicksort Sieve Treesort SymbolicDiff LambdaInterp.

(** NQueens extractions *)
Definition nqueens_8 : nat := nqueens 8.
Definition nqueens_10 : nat := nqueens 10.
Definition nqueens_11 : nat := nqueens 11.

Peregrine Extract "nqueens_8.ast" nqueens_8.
Peregrine Extract "nqueens_10.ast" nqueens_10.
Peregrine Extract "nqueens_11.ast" nqueens_11.

(** Ackermann extractions *)
Definition ackermann_3_9 : nat := ackermann 3 9.
Definition ackermann_3_10 : nat := ackermann 3 10.
Definition ackermann_3_11 : nat := ackermann 3 11.

Peregrine Extract "ackermann_3_9.ast" ackermann_3_9.
Peregrine Extract "ackermann_3_10.ast" ackermann_3_10.
Peregrine Extract "ackermann_3_11.ast" ackermann_3_11.

(** Tak extractions *)
Definition tak_18_12_6 : Z := tak 18 12 6.
Definition tak_21_14_7 : Z := tak 21 14 7.
Definition tak_24_16_8 : Z := tak 24 16 8.

Peregrine Extract "tak_18_12_6.ast" tak_18_12_6.
Peregrine Extract "tak_21_14_7.ast" tak_21_14_7.
Peregrine Extract "tak_24_16_8.ast" tak_24_16_8.

(** Quicksort extractions *)
Definition quicksort_100 : Uint63.int := quicksort_bench 100.
Definition quicksort_500 : Uint63.int := quicksort_bench 500.
Definition quicksort_1000 : Uint63.int := quicksort_bench 1000.

Peregrine Extract "quicksort_100.ast" quicksort_100.
Peregrine Extract "quicksort_500.ast" quicksort_500.
Peregrine Extract "quicksort_1000.ast" quicksort_1000.

(** Sieve extractions *)
Definition sieve_1000 : nat := count_primes 1000.
Definition sieve_5000 : nat := count_primes 5000.
Definition sieve_10000 : nat := count_primes 10000.

Peregrine Extract "sieve_1000.ast" sieve_1000.
Peregrine Extract "sieve_5000.ast" sieve_5000.
Peregrine Extract "sieve_10000.ast" sieve_10000.

(** Treesort extractions *)
Definition treesort_100 : Uint63.int := treesort_bench 100.
Definition treesort_500 : Uint63.int := treesort_bench 500.
Definition treesort_1000 : Uint63.int := treesort_bench 1000.

Peregrine Extract "treesort_100.ast" treesort_100.
Peregrine Extract "treesort_500.ast" treesort_500.
Peregrine Extract "treesort_1000.ast" treesort_1000.

(** Symbolic differentiation extractions *)
Definition symbdiff_10 : nat := symbolic_diff_bench 10.
Definition symbdiff_20 : nat := symbolic_diff_bench 20.
Definition symbdiff_50 : nat := symbolic_diff_bench 50.

Peregrine Extract "symbdiff_10.ast" symbdiff_10.
Peregrine Extract "symbdiff_20.ast" symbdiff_20.
Peregrine Extract "symbdiff_50.ast" symbdiff_50.

(** Lambda interpreter extractions *)
Definition lambda_fact_10 : Z := lambda_interp_bench 10.
Definition lambda_fact_12 : Z := lambda_interp_bench 12.
Definition lambda_church_5 : Z := church_bench 5.

Peregrine Extract "lambda_fact_10.ast" lambda_fact_10.
Peregrine Extract "lambda_fact_12.ast" lambda_fact_12.
Peregrine Extract "lambda_church_5.ast" lambda_church_5.
