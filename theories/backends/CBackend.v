From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.

Local Open Scope bs_scope.



Definition default_c_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition c_phases := {|
  implement_box'  := Required;
  implement_lazy' := Compatible false;
  cofix_to_laxy'  := Compatible false;
  betared'        := Compatible false;
  unboxing'       := Compatible false;
|}.
