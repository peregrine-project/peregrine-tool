From ExtLib.Structures Require Import Monad.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From CertiCoq Require Import Compiler.pipeline.
From CertiCoq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import PAst.
From Peregrine Require Import CertiCoqBackend.
From Peregrine Require Serialize.
From MetaRocq.Erasure.Typed Require Import ResultMonad.

Import MonadNotation.
#[local]
Existing Instance Monad_result.

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

Definition extract_untyped_ast (p : EAst.program)
                               : result string string :=
  Ok (Serialize.string_of_PAst (Untyped p.1 (Some p.2))).

Definition extract_typed_ast (p : ExAst.global_env)
                             : result string string :=
  Ok (Serialize.string_of_PAst (Typed p None)).

Definition extract_mut_ast (remaps : constant_remappings)
                           (opts : certicoq_config)
                           (p : EAst.program)
                           : result string string :=
  Ok "TODO".

Definition extract_local_ast (remaps : constant_remappings)
                             (opts : certicoq_config)
                             (p : EAst.program)
                            : result string string :=
  Ok "TODO".

Definition extract_anf_ast (remaps : constant_remappings)
                           (opts : certicoq_config)
                           (p : EAst.program)
                           : result string string :=
  Ok "TODO".

Definition extract_anfc_ast (remaps : constant_remappings)
                            (opts : certicoq_config)
                            (p : EAst.program)
                            : result string string :=
  Ok "TODO".

Definition extract_ast (remaps : constant_remappings)
                       (custom_attr : custom_attributes)
                       (opts : ast_config)
                       (file_name : string)
                       (p : PAst.PAst)
                       : result string string :=
  match opts.(ast_type) with
  | LambdaBox =>
    (* Cannot use monad notation due to extlib/metarocq clash *)
    match PAst_to_EAst p with
    | Ok p => extract_untyped_ast p
    | Err e => Err e
    end
  | LambdaBoxTyped =>
    match PAst_to_ExAst p with
    | Ok p => extract_typed_ast p
    | Err e => Err e
    end
  | LambdaBoxMut c =>
    match PAst_to_EAst p with
    | Ok p => extract_mut_ast remaps c p
    | Err e => Err e
    end
  | LambdaBoxLocal c =>
    match PAst_to_EAst p with
    | Ok p => extract_local_ast remaps c p
    | Err e => Err e
    end
  | LambdaANF c =>
    match PAst_to_EAst p with
    | Ok p => extract_anf_ast remaps c p
    | Err e => Err e
    end
  | LambdaANFC c =>
    match PAst_to_EAst p with
    | Ok p => extract_anfc_ast remaps c p
    | Err e => Err e
    end
  end.
