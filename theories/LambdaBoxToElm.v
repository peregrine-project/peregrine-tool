From Stdlib Require Import List.
From Stdlib Require Import String.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require Import ExAst.
From TypedExtraction Require Import PrettyPrinterMonad.
From TypedExtraction Require Import ElmExtract.
From TypedExtraction Require Import Common.
From MetaRocq.Erasure.Typed Require Import ResultMonad.
From Peregrine Require Import TypedTransforms.

Import ListNotations.
Import MRMonadNotation.

Local Open Scope bs_scope.



#[local]
Instance ElmBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()"; (* the inhabitant of the unit type *)
     type_box_symbol := "()"; (* unit type *)
     any_type_symbol := "()"; (* unit type *)
     false_elim_def := "false_rec ()"; (* predefined function *)
     print_full_names := true (* short names for readability *)|}.

Definition default_preamble : string := elm_false_rec.

Definition mk_preamble mod_name preamble :=
  let preamble :=
    match preamble with
    | None => ""
    | Some s => s
    end
  in
  "module " ++ mod_name ++ " exposing (..)" ++ nl ++ preamble ++ nl ++ elm_false_rec.

Definition default_remaps : list (kername * string) := [].

Definition box_to_elm mod_name (preamble : option string) (remaps : list (kername * string)) params (Σ : ExAst.global_env) : result string string :=
  let remaps_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') remaps) in
  let preamble := mk_preamble mod_name preamble in
  Σ <- typed_transfoms params Σ;;
  '(_, s) <- (finish_print (print_env Σ remaps_fun));;
  ret (preamble ++ nl ++ s ++ nl).
