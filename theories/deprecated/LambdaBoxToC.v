From MetaRocq.Erasure Require EAst.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import CertiCoqPipeline.
From ExtLib.Structures Require Import Monad.
From Stdlib Require Import ZArith.

Import MonadNotation.



Definition next_id := 100%positive.

Definition box_to_c (p : EAst.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv ;;
  p_anf <- anf_pipeline p prs next_id;;
  compile_Clight prs p_anf.

Definition run_translation (opts : Options) (p : EAst.program) :=
    run_pipeline EAst.program Cprogram opts p box_to_c.
