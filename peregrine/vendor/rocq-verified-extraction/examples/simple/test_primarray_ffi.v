From Malfunction Require Import utils_array.
From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Primitive.
From VerifiedExtraction Require Import Extraction OCamlFFI.

Set Verified Extraction Build Directory "_build".

(* Primitives *)

From Stdlib Require Import PrimInt63 Uint63 PArray.

Definition val : array nat := PArray.make 3 2.

Definition gettest : nat := PArray.get val 2. 
Definition settest : array nat := PArray.set val 2 1. 
Definition getsettest : nat := PArray.get settest 2.

Set Warnings "-primitive-turned-into-axiom".

Definition prim_array_get := (print_int (int_of_nat gettest)).
Definition prim_array_get_set := (print_int (int_of_nat getsettest)).

Verified Extraction -fmt -typed -compile-with-coq val "val.mlf".
Verified Extraction -fmt -typed -unsafe -compile-with-coq -run prim_array_get "prim_array_get.mlf".
Verified Extraction -fmt -typed -compile-with-coq -run prim_array_get_set "prim_array_get_set.mlf".