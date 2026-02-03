From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.

Local Open Scope bs_scope.



Definition default_rust_config := {|
  rust_preamble_top       := "";
  rust_preamble_program   := "";
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
|}.

Definition rust_phases := {|
  implement_box'  := Compatible false;
  implement_lazy' := Compatible false;
  cofix_to_laxy'  := Compatible false;
  betared'        := Compatible false;
  unboxing'       := Compatible false;
|}.
