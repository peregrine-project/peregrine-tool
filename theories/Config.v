From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Kernames.
From Malfunction Require Serialize.

Local Open Scope bs_scope.



Section BackendConfig.

  Record rust_config := {
    rust_preamble         : string;
    rust_term_box_symbol  : string;
    rust_type_box_symbol  : string;
    rust_any_type_symbol  : string;
    rust_print_full_names : bool;
  }.

  Record elm_config := {
    elm_preamble         : string;
    elm_module_name      : string;
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

  Inductive backend_config :=
  | Rust  : rust_config -> backend_config
  | Elm   : elm_config -> backend_config
  | C     : c_config -> backend_config
  | Wasm  : wasm_config -> backend_config
  | OCaml : ocaml_config -> backend_config.

End BackendConfig.

Section BackendConfigOptional.
  Definition get_optional {A A' B : Type} (r : A) (r' : A') (p : A -> option B) (p' : A' -> B) : B :=
    match p r with
    | Some x => x
    | None => p' r'
    end.


  (* Rust *)
  Record rust_config' := {
    rust_preamble'          : option string;
    rust_term_box_symbol'   : option string;
    rust_type_box_symbol'   : option string;
    rust_any_type_symbol'   : option string;
    rust_print_full_names'  : option bool;
  }.
  Definition default_rust_config := {|
    rust_preamble         := "";
    rust_term_box_symbol  := "";
    rust_type_box_symbol  := "";
    rust_any_type_symbol  := "";
    rust_print_full_names := false;
  |}. (* TODO: defaults *)
  Definition mk_rust_config (o : rust_config') : rust_config := {|
    rust_preamble         := get_optional o default_rust_config rust_preamble' rust_preamble;
    rust_term_box_symbol  := get_optional o default_rust_config rust_term_box_symbol' rust_term_box_symbol;
    rust_type_box_symbol  := get_optional o default_rust_config rust_type_box_symbol' rust_type_box_symbol;
    rust_any_type_symbol  := get_optional o default_rust_config rust_any_type_symbol' rust_any_type_symbol;
    rust_print_full_names := get_optional o default_rust_config rust_print_full_names' rust_print_full_names;
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
  Definition default_elm_config := {|
    elm_preamble         := "";
    elm_module_name      := "";
    elm_term_box_symbol  := "";
    elm_type_box_symbol  := "";
    elm_any_type_symbol  := "";
    elm_false_elim_def   := "";
    elm_print_full_names := false;
  |}. (* TODO: defaults *)
  Definition mk_elm_config (o : elm_config') : elm_config := {|
    elm_preamble         := get_optional o default_elm_config elm_preamble' elm_preamble;
    elm_module_name      := get_optional o default_elm_config elm_module_name' elm_module_name;
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
  Definition default_certicoq_config := {|
    direct    := false;
    c_args    := 0;
    o_level   := 0;
    prefix    := "";
    body_name := "";
  |}. (* TODO: defaults *)
  Definition mk_certicoq_config (o : certicoq_config') : certicoq_config := {|
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
  Definition default_ocaml_config := {|
    program_type := Malfunction.Serialize.Standalone
  |}.
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
    | C' o => C (mk_certicoq_config o)
    | Wasm' o => Wasm (mk_certicoq_config o)
    | OCaml' o => OCaml (mk_ocaml_config o)
    end.

End BackendConfigOptional.
