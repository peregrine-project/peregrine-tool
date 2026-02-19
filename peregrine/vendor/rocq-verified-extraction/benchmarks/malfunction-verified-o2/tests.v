Require Import VerifiedExtraction.Benchmarks.lib.tests.
From VerifiedExtraction Require Import Extraction.
From MetaRocq.Utils Require Import bytestring.

Open Scope bs.

Eval compute in "Compiling demo0".

Verified Extraction demo0 "demo0.mlf".

Eval compute in "Compiling demo1".

Verified Extraction demo1 "demo1.mlf".

Eval compute in "Compiling demo2".

Verified Extraction demo2 "demo2.mlf".

Eval compute in "Compiling demo3".

Verified Extraction demo3 "demo3.mlf".

Eval compute in "Compiling list_sum".

Verified Extraction list_sum "list_sum.mlf".

Eval compute in "Compiling vs_easy".

Verified Extraction vs_easy "vs_easy.mlf".

Eval compute in "Compiling vs_hard".

Verified Extraction vs_hard "vs_hard.mlf".

Eval compute in "Compiling binom".

Verified Extraction binom "binom.mlf".

(* Eval compute in "Compiling lazy factorial". *)

(* (* CertiRocq Compile -O 1 lazy_factorial. *)
(* CertiRocq Compile -ext "_opt" lazy_factorial. *)
(* CertiRocq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" lazy_factorial. *) *)
(* (* CertiRocq Compile -O 0 -cps -ext "_cps" demo1. *) *)
(* (* CertiRocq Compile -cps -ext "_cps_opt" demo1. *) *)

Eval compute in "Compiling color".

Verified Extraction color "color.mlf".

(* (* Don't compile slow sha *) *)
(* (* Eval compute in "Compiling sha". *) *)

(* (* CertiRocq Compile -cps -ext "_cps" sha. *) *)
(* (* CertiRocq Compile sha. *) *)
(* (* CertiRocq Compile -O 1 -cps -ext "_cps_opt" sha. *) *)
(* (* CertiRocq Compile -O 1 -ext "_opt" sha. *) *)

Eval compute in "Compiling sha_fast".

Verified Extraction sha_fast "sha_fast.mlf".
