From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiCoqBackend.
From Peregrine Require Import EvalBox.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_eval_config := {|
  copts           := {|
    direct    := true;
    c_args    := 5;
    o_level   := 0;
    anf_conf  := 0;
    prefix    := "";
    body_name := "body";
  |};
  Config.fuel     := (Nat.pow 2 14);
  Config.eval_anf := true;
|}.

Definition eval_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
|}.



Definition eval_anf_pipeline prs fuel (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  p_anf <- anf_pipeline p prs next_id;;
  (* Eval using ANF evaluator *)
  p_v <- eval_anf fuel p_anf;;
  ret p_v.

Definition eval_mut_pipeline prs fuel (p : EAst.program) :=
  let env := p.1 in
  '(prs, next_id) <- register_prims prs next_id env ;;
  p_anf <- mut_pipeline p prs;;
  (* Eval using mut evaluator *)
  p_v <- eval_mut fuel p_anf;;
  ret p_v.



Definition eval (remaps : constant_remappings)
                (custom_attr : custom_attributes)
                (opts : eval_config)
                (file_name : string)
                (p : EAst.program)
                : result string string :=
  let config := mk_opts opts.(Config.copts) in
  let prs := mk_prims remaps in
  let evaluator := if opts.(Config.eval_anf) then eval_anf_pipeline else eval_mut_pipeline in
  let (res, _) :=
    run_pipeline EAst.program string config p (evaluator prs opts.(Config.fuel)) in
  match res with
  | compM.Ret s => Ok s
  | compM.Err s => Err s
  end.
