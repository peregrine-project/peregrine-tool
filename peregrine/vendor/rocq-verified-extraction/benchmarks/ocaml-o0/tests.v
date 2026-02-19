Require Import Arith List String.
Require Import VerifiedExtraction.Benchmarks.lib.vs.
Require Import VerifiedExtraction.Benchmarks.lib.Binom.
Require Import VerifiedExtraction.Benchmarks.lib.Color.
Require Import VerifiedExtraction.Benchmarks.lib.sha256.
Require Import VerifiedExtraction.Benchmarks.lib.tests.

Set Extraction Output Directory ".".

Open Scope string.

(* The same benchmarks as CertiCoq benchmarks, but slightly modified
   to suspend computations with unit so we can run multiple times *)

Extraction "demo0" demo0.
Extraction "demo1" demo1.
Extraction "demo2" demo2.
Extraction "demo2" demo2.
Extraction "list_sum" list_sum.
(* Modified by hand *)
Extraction "vs_easy" vs_easy.
(* Modified by hand *)
Extraction "vs_hard" vs_hard.
(* Definition binom (_ : unit) := Binom.main. *)
Extraction "binom" binom.
(* Does not typecheck *)
(* Extraction "color" color. *)
Extraction "sha" sha.
Extraction "sha_fast" sha_fast.
