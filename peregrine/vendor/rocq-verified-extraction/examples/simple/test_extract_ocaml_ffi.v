From VerifiedExtraction Require Import Extraction.
From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import bytestring.
From VerifiedExtraction Require Import OCamlFFI.

Set Verified Extraction Build Directory "_build".

Definition hello_world :=
  print_string "Hello world!"%bs.

Verified Extraction -fmt -compile-with-coq -run hello_world "hello_world.mlf".
