From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Kernames.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import RustBackend.
From Peregrine Require Import ElmBackend.
From Peregrine Require Import OCamlBackend.
From Peregrine Require Import CBackend.
From Peregrine Require Import WasmBackend.

Local Open Scope bs_scope.


Section ErasureConfig.

  Definition mk_opts (c : config) (typed : bool) : erasure_configuration := {|
      enable_unsafe := {|
        Erasure.cofix_to_lazy := c.(erasure_opts).(phases).(cofix_to_laxy);
        Erasure.inlining := true;
        Erasure.unboxing := c.(erasure_opts).(phases).(unboxing);
        Erasure.betared := c.(erasure_opts).(phases).(betared);
      |};
      dearging_config := {|
        overridden_masks := fun _ => None;
        do_trim_const_masks := c.(erasure_opts).(dearging_do_trim_const_masks);
        do_trim_ctor_masks := c.(erasure_opts).(dearging_do_trim_ctor_masks);
      |};
      enable_typed_erasure := typed;
      inlined_constants := MetaRocq.Erasure.Typed.Utils.kername_set_of_list c.(inlinings_opts)
    |}.

  Definition mk_cstr_reorders (c : config) := c.(cstr_reorders_opts).

End ErasureConfig.



Section BackendConfigOptional.
  Definition get_optional {A A' B : Type} (r : A) (r' : A') (p : A -> option B) (p' : A' -> B) : B :=
    match p r with
    | Some x => x
    | None => p' r'
    end.


  (* Rust *)
  Record rust_config' := {
    rust_preamble_top'       : option string;
    rust_preamble_program'   : option string;
    rust_term_box_symbol'    : option string;
    rust_type_box_symbol'    : option string;
    rust_any_type_symbol'    : option string;
    rust_print_full_names'   : option bool;
    rust_default_attributes' : option string;
  }.

  Definition mk_rust_config (o : rust_config') : rust_config := {|
    rust_preamble_top       := get_optional o default_rust_config rust_preamble_top' rust_preamble_top;
    rust_preamble_program   := get_optional o default_rust_config rust_preamble_program' rust_preamble_program;
    rust_term_box_symbol    := get_optional o default_rust_config rust_term_box_symbol' rust_term_box_symbol;
    rust_type_box_symbol    := get_optional o default_rust_config rust_type_box_symbol' rust_type_box_symbol;
    rust_any_type_symbol    := get_optional o default_rust_config rust_any_type_symbol' rust_any_type_symbol;
    rust_print_full_names   := get_optional o default_rust_config rust_print_full_names' rust_print_full_names;
    rust_default_attributes := get_optional o default_rust_config rust_default_attributes' rust_default_attributes;
  |}.


  (* Elm *)
  Record elm_config' := {
    elm_preamble'         : option string;
    elm_module_name'      : option string;
    elm_term_box_symbol'  : option string;
    elm_type_box_symbol'  : option string;
    elm_any_type_symbol'  : option string;
    elm_false_elim_def'   : option string;
    elm_print_full_names' : option bool;
  }.

  Definition mk_elm_config (o : elm_config') : elm_config := {|
    elm_preamble         := get_optional o default_elm_config elm_preamble' elm_preamble;
    elm_module_name      :=
      match o.(elm_module_name') with
      | None => default_elm_config.(elm_module_name)
      | Some s => Some s
      end;
    elm_term_box_symbol  := get_optional o default_elm_config elm_term_box_symbol' elm_term_box_symbol;
    elm_type_box_symbol  := get_optional o default_elm_config elm_type_box_symbol' elm_type_box_symbol;
    elm_any_type_symbol  := get_optional o default_elm_config elm_any_type_symbol' elm_any_type_symbol;
    elm_false_elim_def   := get_optional o default_elm_config elm_false_elim_def' elm_false_elim_def;
    elm_print_full_names := get_optional o default_elm_config elm_print_full_names' elm_print_full_names;
  |}.

  (* C and Wasm *)
  Record certicoq_config' := {
    direct'    : option bool;
    c_args'    : option nat;
    o_level'   : option nat;
    prefix'    : option string;
    body_name' : option string;
  }.

  Definition mk_certicoq_config default_certicoq_config (o : certicoq_config') : certicoq_config := {|
    direct    := get_optional o default_certicoq_config direct' direct;
    c_args    := get_optional o default_certicoq_config c_args' c_args;
    o_level   := get_optional o default_certicoq_config o_level' o_level;
    prefix    := get_optional o default_certicoq_config prefix' prefix;
    body_name := get_optional o default_certicoq_config body_name' body_name;
  |}.

  Definition c_config' : Type := certicoq_config'.

  Definition wasm_config' : Type := certicoq_config'.

  (* OCaml *)
  Record ocaml_config' := {
    program_type' : option Malfunction.Serialize.program_type;
  }.

  Definition mk_ocaml_config (o : ocaml_config') : ocaml_config := {|
    program_type := get_optional o default_ocaml_config program_type' program_type;
  |}.

  Inductive backend_config' :=
  | Rust' : rust_config' -> backend_config'
  | Elm' : elm_config' -> backend_config'
  | C' : c_config' -> backend_config'
  | Wasm' : wasm_config' -> backend_config'
  | OCaml' : ocaml_config' -> backend_config'.
  Definition mk_backend_config (o : backend_config') : backend_config :=
    match o with
    | Rust' o => Rust (mk_rust_config o)
    | Elm' o => Elm (mk_elm_config o)
    | C' o => C (mk_certicoq_config default_c_config o)
    | Wasm' o => Wasm (mk_certicoq_config default_wasm_config o)
    | OCaml' o => OCaml (mk_ocaml_config o)
    end.

End BackendConfigOptional.



Section GeneralConfigOptional.

  Definition get_default_phase_opt' (o : erasure_phases') (p : erasure_phases' -> phases_config) : bool :=
    match (p o) with
    | Required => true
    | Compatible default => default
    | Incompatible => false
    end.

  Definition get_default_phases_opt (o : erasure_phases') := {|
    implement_box  := get_default_phase_opt' o implement_box';
    implement_lazy := get_default_phase_opt' o implement_lazy';
    cofix_to_laxy  := get_default_phase_opt' o cofix_to_laxy';
    betared        := get_default_phase_opt' o betared';
    unboxing       := get_default_phase_opt' o unboxing';
  |}.

  Definition enforce_phase' (b : bool) (o : phases_config) : bool :=
    match o with
    | Required => true
    | Incompatible => false
    | _ => b
    end.

  Definition enforce_phases (o : erasure_phases) (o' : erasure_phases') : erasure_phases := {|
    implement_box  := enforce_phase' o.(implement_box)  o'.(implement_box');
    implement_lazy := enforce_phase' o.(implement_lazy) o'.(implement_lazy');
    cofix_to_laxy  := enforce_phase' o.(cofix_to_laxy)  o'.(cofix_to_laxy');
    betared        := enforce_phase' o.(betared)        o'.(betared');
    unboxing       := enforce_phase' o.(unboxing)       o'.(unboxing');
  |}.

  Definition mk_erasure_phases (b : backend_config') (o : option erasure_phases) : erasure_phases :=
    match o with
    | Some o =>
      match b with
      | Rust' _  => enforce_phases o rust_phases
      | Elm' _   => enforce_phases o elm_phases
      | C' _     => enforce_phases o c_phases
      | Wasm' _  => enforce_phases o wasm_phases
      | OCaml' _ => enforce_phases o ocaml_phases
      end
    | None =>
      match b with
      | Rust' _  => get_default_phases_opt rust_phases
      | Elm' _   => get_default_phases_opt elm_phases
      | C' _     => get_default_phases_opt c_phases
      | Wasm' _  => get_default_phases_opt wasm_phases
      | OCaml' _ => get_default_phases_opt ocaml_phases
      end
    end.

  Record erasure_config' := {
      phases'                       : option erasure_phases;
      dearging_do_trim_const_masks' : option bool;
      dearging_do_trim_ctor_masks'  : option bool;
    }.
  Definition mk_erasure_config (b : backend_config') (o : erasure_config') : erasure_config := {|
    phases := mk_erasure_phases b o.(phases');
    dearging_do_trim_const_masks :=
      match o.(dearging_do_trim_const_masks') with
      | Some x => x
      | None => true
      end;
    dearging_do_trim_ctor_masks :=
      match o.(dearging_do_trim_ctor_masks') with
      | Some x => x
      | None => true
      end;
  |}.

  Record config' := {
      backend_opts'           : backend_config';
      erasure_opts'           : erasure_config';
      inlinings_opts'         : inlinings;
      remappings_opts'        : remappings;
      cstr_reorders_opts'     : EProgram.inductives_mapping;
      custom_attributes_opts' : custom_attributes;
    }.
  Definition mk_config (o : config') : config := {|
    backend_opts           := mk_backend_config o.(backend_opts');
    erasure_opts           := mk_erasure_config o.(backend_opts') o.(erasure_opts');
    inlinings_opts         := o.(inlinings_opts');
    remappings_opts        := o.(remappings_opts');
    cstr_reorders_opts     := o.(cstr_reorders_opts');
    custom_attributes_opts := o.(custom_attributes_opts');
  |}.

End GeneralConfigOptional.
