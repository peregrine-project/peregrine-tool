(** * Peregrine Extraction for QuicksortZ benchmark *)

From Peregrine Require Import Loader.
From BenchmarksGame Require Import QuicksortZ.

Peregrine Extract "quicksort_z_10.ast" quicksort_z_10.
Peregrine Extract "quicksort_z_100.ast" quicksort_z_100.
Peregrine Extract "quicksort_z_500.ast" quicksort_z_500.
Peregrine Extract "quicksort_z_1000.ast" quicksort_z_1000.
