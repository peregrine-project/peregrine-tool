From Malfunction.Plugin Require Import Extract.
From Malfunction Require Import Pipeline.

Set Verified Extraction Build Directory "_build".

Unset Verified Extraction Use Opam.

(* Malfunction.Plugin.Extract binds all primitives to OCaml externals *)
Set Warnings "-primitive-turned-into-axiom".

(* MetaRocq Run Print mli compile_malfunction_gen. *)
Verified Extraction -fmt compile_malfunction_gen "compile_malfunction.mlf".
