From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.

Local Open Scope bs_scope.



Definition default_elm_config := {|
  elm_preamble         := "";
  elm_module_name      := None;
  elm_term_box_symbol  := "()";
  elm_type_box_symbol  := "()";
  elm_any_type_symbol  := "()";
  elm_false_elim_def   := "false_rec ()";
  elm_print_full_names := true;
|}.

Definition elm_phases := {|
  implement_box'  := Compatible false;
  implement_lazy' := Compatible false;
  cofix_to_laxy'  := Compatible false;
  betared'        := Compatible false;
  unboxing'       := Compatible false;
|}.
