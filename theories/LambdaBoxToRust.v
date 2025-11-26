From Stdlib Require Import List.
From Stdlib Require Import String.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Erasure Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From RustExtraction Require Import PrettyPrinterMonad.
From RustExtraction Require Import Printing.
From RustExtraction Require Import RustExtract.
From LambdaBox Require Import TypedTransforms.

Import ListNotations.
Import MRMonadNotation.



#[local]
Instance plugin_extract_preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]";
"#![allow(non_camel_case_types)]";
"#![allow(unused_imports)]";
"#![allow(non_snake_case)]";
"#![allow(unused_variables)]";
"";
"use std::marker::PhantomData;";
"";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
"  f";
"}" ];
program_preamble := [
"fn alloc<T>(&'a self, t: T) -> &'a T {";
"  self.__alloc.alloc(t)";
"}";
"";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)";
"}" ] |}.

#[local]
Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := true |}.

Definition default_attrs : ind_attr_map := fun _ => "#[derive(Debug, Clone)]".

Definition default_remaps : remaps := no_remaps.

Definition mk_preamble top program :=
   {|
      top_preamble :=
         match top with
         | Some top => (@top_preamble plugin_extract_preamble) ++ [top]
         | None => (@top_preamble plugin_extract_preamble)
         end;
      program_preamble :=
         match program with
         | Some program => (@program_preamble plugin_extract_preamble) ++ [program]
         | None => (@program_preamble plugin_extract_preamble)
         end;
   |}.

Definition box_to_rust (remaps : remaps) preamble attrs params (Σ : ExAst.global_env) : result (list string) string :=
   Σ <- typed_transfoms params Σ;;
   let p := @print_program Σ remaps RustConfig attrs preamble in
   '(_, s) <- MetaRocq.Erasure.Typed.Utils.timed "Printing" (fun _ => (finish_print_lines p));;
   Ok s.
