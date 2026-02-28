From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import PAst.
From Peregrine Require Import CertiCoqBackend.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_ast_config := {|
  ast_type := LambdaBox;
|}.

Definition default_ast_c_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition ast_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
|}.



Definition extract_ast (remaps : constant_remappings)
                       (custom_attr : custom_attributes)
                       (opts : ast_config)
                       (file_name : string)
                       (p : PAst.PAst)
                       : result string string :=
  match opts.(ast_type) with
  | LambdaBox => Ok "TODO"
  | LambdaBoxTyped => Ok "TODO"
  | LambdaBoxMut c => Ok "TODO"
  | LambdaBoxLocal c => Ok "TODO"
  | LambdaANF c => Ok "TODO"
  | LambdaANFC c => Ok "TODO"
  end.
