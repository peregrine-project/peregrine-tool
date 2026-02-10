From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Kernames.
From Malfunction Require Serialize.

Local Open Scope bs_scope.



Section BackendConfig.

  Record rust_config := {
    rust_preamble_top       : string;
    rust_preamble_program   : string;
    rust_term_box_symbol    : string;
    rust_type_box_symbol    : string;
    rust_any_type_symbol    : string;
    rust_print_full_names   : bool;
    rust_default_attributes : string;
  }.

  Record elm_config := {
    elm_preamble         : string;
    elm_module_name      : option string;
    elm_term_box_symbol  : string;
    elm_type_box_symbol  : string;
    elm_any_type_symbol  : string;
    elm_false_elim_def   : string;
    elm_print_full_names : bool;
  }.

  Record certicoq_config := {
    direct    : bool;
    c_args    : nat;
    o_level   : nat;
    prefix    : string;
    body_name : string;
  }.

  Definition c_config : Type := certicoq_config.

  Definition wasm_config : Type := certicoq_config.

  Record ocaml_config := {
    program_type : Malfunction.Serialize.program_type;
  }.

  Definition cakeml_config : Type := unit.

  Inductive backend_config :=
  | Rust   : rust_config -> backend_config
  | Elm    : elm_config -> backend_config
  | C      : c_config -> backend_config
  | Wasm   : wasm_config -> backend_config
  | OCaml  : ocaml_config -> backend_config
  | CakeML : cakeml_config -> backend_config.

End BackendConfig.



Section GeneralConfig.

  Record remapped_inductive := build_remapped_inductive {
      re_ind_name  : string;
      re_ind_ctors : list string;
      re_ind_match : option string;
    }.

  Definition external_remapping : Type := option string.
  Definition arity : Type := option nat.

  Inductive remapping :=
  | RemapInductive      : Kernames.inductive -> external_remapping -> remapped_inductive -> remapping
  | RemapConstant       : Kernames.kername -> external_remapping -> arity -> bool -> string -> remapping
  | RemapInlineConstant : Kernames.kername -> external_remapping -> arity -> bool -> string -> remapping.

  Definition custom_attribute : Type := (Kernames.kername * string).

  Definition inlinings : Type := list Kernames.kername.
  Definition remappings : Type := list remapping.
  Definition custom_attributes : Type := list custom_attribute.

  Inductive phases_config :=
  | Required : phases_config
  | Compatible (default : bool) : phases_config
  | Incompatible : phases_config.

  Record erasure_phases_config := {
      implement_box_c  : phases_config;
      implement_lazy_c : phases_config;
      cofix_to_laxy_c  : phases_config;
      betared_c        : phases_config;
      unboxing_c       : phases_config;
      dearg_ctors_c    : phases_config;
      dearg_consts_c   : phases_config;
    }.

  Record erasure_phases := {
      implement_box  : bool;
      implement_lazy : bool;
      cofix_to_laxy  : bool;
      betared        : bool;
      unboxing       : bool;
      dearg_ctors    : bool;
      dearg_consts   : bool;
    }.

  Record config := {
      backend_opts           : backend_config;
      erasure_opts           : erasure_phases;
      inlinings_opts         : inlinings;
      remappings_opts        : remappings;
      cstr_reorders_opts     : EProgram.inductives_mapping;
      custom_attributes_opts : custom_attributes;
    }.

  Record attributes_config := {
      inlinings_opt         : inlinings;
      remappings_opt        : remappings;
      cstr_reorders_opt     : EProgram.inductives_mapping;
      custom_attributes_opt : custom_attributes;
    }.

End GeneralConfig.
