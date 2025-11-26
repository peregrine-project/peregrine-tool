From MetaRocq.Erasure Require EAst.
From MetaRocq.Utils Require Import bytestring.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import CodegenWasm.toplevel.
From CertiCoq Require Import Common.Pipeline_utils.
From LambdaBox Require Import CertiCoqPipeline.
From ExtLib.Structures Require Import Monad.
From Wasm Require Import binary_format_printer.
From Stdlib Require Import ZArith.

Import MonadNotation.



Definition print_wasm p := (String.parse (binary_of_module p)).

Definition box_to_wasm (p : EAst.program) :=
  let genv := fst p in
  '(prs, next_id) <- register_prims next_id genv ;; (* TODO: better prim registration *)
  p_anf <- anf_pipeline p prs next_id;;
  (* Compile lambda_anf -> WASM *)
  p_wasm <- compile_LambdaANF_to_Wasm prs p_anf;;
  ret (print_wasm p_wasm).

Definition run_translation (opts : Options) (p : EAst.program) :=
    run_pipeline EAst.program string opts p box_to_wasm.
