From VerifiedExtraction Require Import Extraction.

From compcert Require Import Compiler.

Verified Extraction transf_c_program "compcert.mlf".

(* From MetaRocq Require Import bytestring. *)
(* Open Scope bs. *)
(* MetaRocq Run Print mli transf_c_program. *)
