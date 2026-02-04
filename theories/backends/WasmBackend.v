From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From CertiCoq Require Import CodegenWasm.toplevel.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiCoqBackend.
From Wasm Require Import binary_format_printer.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_wasm_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition wasm_phases := {|
  implement_box'  := Required;
  implement_lazy' := Compatible false;
  cofix_to_laxy'  := Compatible false;
  betared'        := Compatible false;
  unboxing'       := Compatible false;
|}.



Definition wasm_pipeline prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  p_anf <- anf_pipeline p prs next_id;;
  (* Compile lambda_anf -> WASM *)
  p_wasm <- compile_LambdaANF_to_Wasm prs p_anf;;
  ret p_wasm.

Definition print_wasm p : string :=
  String.parse (binary_of_module p).


Definition extract_wasm (remaps : remappings)
                        (custom_attr : custom_attributes)
                        (opts : wasm_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result string string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) := run_pipeline EAst.program _ config p (wasm_pipeline prs) in
  match res with
  | compM.Ret m => Ok (print_wasm m)
  | compM.Err s => Err s
  end.
