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
From Peregrine Require Import CakeMLBackend.
From Peregrine Require Import CBackend.
From Peregrine Require Import WasmBackend.

Local Open Scope bs_scope.


Section ErasureConfig.

  Definition mk_opts (c : config) (typed : bool) : erasure_configuration := {|
      enable_unsafe := {|
        Erasure.cofix_to_lazy := c.(erasure_opts).(cofix_to_laxy);
        Erasure.inlining := true;
        Erasure.unboxing := c.(erasure_opts).(unboxing);
        Erasure.betared := c.(erasure_opts).(betared);
      |};
      dearging_config := {|
        overridden_masks := fun _ => None;
        do_trim_const_masks := c.(erasure_opts).(dearg_consts);
        do_trim_ctor_masks := c.(erasure_opts).(dearg_ctors);
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
  Definition empty_rust_config' : rust_config' := {|
    rust_preamble_top'       := None;
    rust_preamble_program'   := None;
    rust_term_box_symbol'    := None;
    rust_type_box_symbol'    := None;
    rust_any_type_symbol'    := None;
    rust_print_full_names'   := None;
    rust_default_attributes' := None;
  |}.

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
  Definition empty_elm_config' : elm_config' := {|
    elm_preamble'         := None;
    elm_module_name'      := None;
    elm_term_box_symbol'  := None;
    elm_type_box_symbol'  := None;
    elm_any_type_symbol'  := None;
    elm_false_elim_def'   := None;
    elm_print_full_names' := None;
  |}.

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
  Definition empty_certicoq_config' : certicoq_config' := {|
    direct'    := None;
    c_args'    := None;
    o_level'   := None;
    prefix'    := None;
    body_name' := None;
  |}.

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
  Definition empty_ocaml_config' : ocaml_config' := {|
    program_type' := None;
  |}.

  Definition mk_ocaml_config (o : ocaml_config') : ocaml_config := {|
    program_type := get_optional o default_ocaml_config program_type' program_type;
  |}.

  Definition cakeml_config' : Type := unit.
  Definition empty_cakeml_config' : cakeml_config' := tt.

  Definition mk_cakeml_config (o : cakeml_config') : cakeml_config := tt.

  Inductive backend_config' :=
  | Rust'   : rust_config' -> backend_config'
  | Elm'    : elm_config' -> backend_config'
  | C'      : c_config' -> backend_config'
  | Wasm'   : wasm_config' -> backend_config'
  | OCaml'  : ocaml_config' -> backend_config'
  | CakeML' : cakeml_config' -> backend_config'.
  Definition mk_backend_config (o : backend_config') : backend_config :=
    match o with
    | Rust' o   => Rust (mk_rust_config o)
    | Elm' o    => Elm (mk_elm_config o)
    | C' o      => C (mk_certicoq_config default_c_config o)
    | Wasm' o   => Wasm (mk_certicoq_config default_wasm_config o)
    | OCaml' o  => OCaml (mk_ocaml_config o)
    | CakeML' o => CakeML (mk_cakeml_config o)
    end.

End BackendConfigOptional.



Section GeneralConfigOptional.

  Record erasure_phases' := {
    implement_box'  : option bool;
    implement_lazy' : option bool;
    cofix_to_laxy'  : option bool;
    betared'        : option bool;
    unboxing'       : option bool;
    dearg_ctors'    : option bool;
    dearg_consts'   : option bool;
  }.
  Definition empty_erasure_phases' : erasure_phases' := {|
    implement_box'  := None;
    implement_lazy' := None;
    cofix_to_laxy'  := None;
    betared'        := None;
    unboxing'       := None;
    dearg_ctors'    := None;
    dearg_consts'   := None;
  |}.

  Definition get_default_phase_opt' (o : erasure_phases_config) (p : erasure_phases_config -> phases_config) : bool :=
    match (p o) with
    | Required => true
    | Compatible default => default
    | Incompatible => false
    end.

  Definition get_default_phases_opt (o : erasure_phases_config) := {|
    implement_box  := get_default_phase_opt' o implement_box_c;
    implement_lazy := get_default_phase_opt' o implement_lazy_c;
    cofix_to_laxy  := get_default_phase_opt' o cofix_to_laxy_c;
    betared        := get_default_phase_opt' o betared_c;
    unboxing       := get_default_phase_opt' o unboxing_c;
    dearg_ctors    := get_default_phase_opt' o dearg_ctors_c;
    dearg_consts   := get_default_phase_opt' o dearg_consts_c;
  |}.

  Definition enforce_phase' (b' : option bool) (b : bool) (o : phases_config) : bool :=
    match o with
    | Required => true
    | Incompatible => false
    | _ =>
      match b' with
      | Some x => x
      | None => b
      end
    end.

  Definition enforce_phases (o : erasure_phases') (d : erasure_phases) (o' : erasure_phases_config) : erasure_phases := {|
    implement_box  := enforce_phase' o.(implement_box')  d.(implement_box)  o'.(implement_box_c);
    implement_lazy := enforce_phase' o.(implement_lazy') d.(implement_lazy) o'.(implement_lazy_c);
    cofix_to_laxy  := enforce_phase' o.(cofix_to_laxy')  d.(cofix_to_laxy)  o'.(cofix_to_laxy_c);
    betared        := enforce_phase' o.(betared')        d.(betared)        o'.(betared_c);
    unboxing       := enforce_phase' o.(unboxing')       d.(unboxing)       o'.(unboxing_c);
    dearg_ctors    := enforce_phase' o.(dearg_ctors')    d.(dearg_ctors)    o'.(dearg_ctors_c);
    dearg_consts   := enforce_phase' o.(dearg_consts')   d.(dearg_consts)   o'.(dearg_consts_c);
  |}.

  Definition mk_erasure_phases (b : backend_config') (o : option erasure_phases') : erasure_phases :=
    let def_opt :=
      match b with
      | Rust' _   => get_default_phases_opt rust_phases
      | Elm' _    => get_default_phases_opt elm_phases
      | C' _      => get_default_phases_opt c_phases
      | Wasm' _   => get_default_phases_opt wasm_phases
      | OCaml' _  => get_default_phases_opt ocaml_phases
      | CakeML' _ => get_default_phases_opt cakeml_phases
      end in
    match o with
    | Some o =>
      match b with
      | Rust' _   => enforce_phases o def_opt rust_phases
      | Elm' _    => enforce_phases o def_opt elm_phases
      | C' _      => enforce_phases o def_opt c_phases
      | Wasm' _   => enforce_phases o def_opt wasm_phases
      | OCaml' _  => enforce_phases o def_opt ocaml_phases
      | CakeML' _ => enforce_phases o def_opt cakeml_phases
      end
    | None => def_opt
    end.

  Definition mk_erasure_config (b : backend_config') (o : option erasure_phases') : erasure_phases :=
    mk_erasure_phases b o.

  Record config' := {
    backend_opts'           : backend_config';
    erasure_opts'           : option erasure_phases';
    inlinings_opts'         : inlinings;
    remappings_opts'        : remappings;
    cstr_reorders_opts'     : EProgram.inductives_mapping;
    custom_attributes_opts' : custom_attributes;
  }.
  Definition empty_config' (b : backend_config') : config' := {|
    backend_opts'           := b;
    erasure_opts'           := None;
    inlinings_opts'         := nil;
    remappings_opts'        := nil;
    cstr_reorders_opts'     := nil;
    custom_attributes_opts' := nil;
  |}.

  Definition mk_config (o : config') : config := {|
    backend_opts           := mk_backend_config o.(backend_opts');
    erasure_opts           := mk_erasure_config o.(backend_opts') o.(erasure_opts');
    inlinings_opts         := o.(inlinings_opts');
    remappings_opts        := o.(remappings_opts');
    cstr_reorders_opts     := o.(cstr_reorders_opts');
    custom_attributes_opts := o.(custom_attributes_opts');
  |}.

  Definition merge_attributes_config (o : config) (attrs : list attributes_config) : config :=
    let inlinings_o :=
      List.concat (o.(inlinings_opts) :: (List.map inlinings_opt attrs)) in
    let remappings_o :=
      List.concat (o.(remappings_opts) :: (List.map remappings_opt attrs)) in
    let cstr_reorders_o :=
      List.concat (o.(cstr_reorders_opts) :: (List.map cstr_reorders_opt attrs)) in
    let custom_attributes_o :=
      List.concat (o.(custom_attributes_opts) :: (List.map custom_attributes_opt attrs)) in
    {|
      backend_opts           := o.(backend_opts);
      erasure_opts           := o.(erasure_opts);
      inlinings_opts         := inlinings_o;
      remappings_opts        := remappings_o;
      cstr_reorders_opts     := cstr_reorders_o;
      custom_attributes_opts := custom_attributes_o;
    |}.



  Definition is_rust_config (o : config) : bool :=
    match o.(backend_opts) with
    | Rust _ => true
    | _ => false
    end.

  Definition is_elm_config (o : config) : bool :=
    match o.(backend_opts) with
    | Elm _ => true
    | _ => false
    end.

  Definition is_ocaml_config (o : config) : bool :=
    match o.(backend_opts) with
    | OCaml _ => true
    | _ => false
    end.

  Definition is_cakeml_config (o : config) : bool :=
    match o.(backend_opts) with
    | CakeML _ => true
    | _ => false
    end.

  Definition is_c_config (o : config) : bool :=
    match o.(backend_opts) with
    | C _ => true
    | _ => false
    end.

  Definition is_wasm_config (o : config) : bool :=
    match o.(backend_opts) with
    | Wasm _ => true
    | _ => false
    end.

End GeneralConfigOptional.
