From Peregrine Require Import Serialize.
From Peregrine Require Import PAst.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import Transforms.
From Peregrine Require Import Erasure.
From Peregrine Require Import CheckWf.
From Peregrine Require LambdaBoxToRust.
From Peregrine Require LambdaBoxToElm.
From Peregrine Require LambdaBoxToOCaml.
From Peregrine Require LambdaBoxToC.
From Peregrine Require LambdaBoxToWasm.
From Peregrine Require TypedTransforms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.

Import MRMonadNotation.

Local Open Scope bs_scope.



Definition parse_ast (s : string) : result PAst string :=
  match PAst_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing input program\n" ++ string_of_error true true e)
  end.

Definition parse_config (s : string) : result config string :=
  match config_of_string s with
  | inr p => Ok (mk_config p)
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition get_config (c : string + config') : result config string :=
  match c with
  | inl s => parse_config s
  | inr c' => Ok (mk_config c')
  end.



Definition peregrine_pipeline (c : string + config') (p : string) (f : string) : extraction_result :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c;; (* Parse or construct config *)
