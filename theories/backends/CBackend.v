From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiCoqBackend.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_c_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition c_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
|}.



Definition c_pipeline prs (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  p_anf <- anf_pipeline p prs next_id;;
  (* Compile lambda_anf to C_light *)
  p_c <- compile_Clight prs p_anf;;
  ret p_c.



Definition extract_c (remaps : remappings)
                     (custom_attr : custom_attributes)
                     (opts : c_config)
                     (file_name : string)
                     (p : EAst.program)
                     : result (Cprogram * list string) string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let gc_lib := if opts.(direct) then "gc_stack.h" else "gc.h" in
  let libs := gc_lib :: (Kernames.IdentSetProp.to_list (get_libs remaps)) in
  let (res, _) := run_pipeline EAst.program Cprogram config p (c_pipeline prs) in
  match res with
  | compM.Ret p => Ok (p, libs)
  | compM.Err s => Err s
  end.
