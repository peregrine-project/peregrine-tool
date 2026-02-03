From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.

Local Open Scope bs_scope.

Definition default_ocaml_config := {|
  program_type := Malfunction.Serialize.Standalone
|}.

Definition ocaml_phases := {|
  implement_box'  := Required;
  implement_lazy' := Compatible false;
  cofix_to_laxy'  := Compatible false;
  betared'        := Compatible false;
  unboxing'       := Compatible true;
|}.
