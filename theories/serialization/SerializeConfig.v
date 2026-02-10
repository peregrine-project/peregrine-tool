From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure Require Import EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import CeresExtra.
From Stdlib Require Import List.
From Ceres Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Serializers *)

(** ** Backend Config *)

Instance Serialize_rust_config : Serialize rust_config :=
  fun o =>
    [Atom "rust_config";
     to_sexp (rust_preamble_top o);
     to_sexp (rust_preamble_program o);
     to_sexp (rust_term_box_symbol o);
     to_sexp (rust_type_box_symbol o);
     to_sexp (rust_any_type_symbol o);
     to_sexp (rust_print_full_names o);
     to_sexp (rust_default_attributes o)
    ]%sexp.

Instance Serialize_rust_config' : Serialize rust_config' :=
  fun o =>
    [Atom "rust_config";
     to_sexp (rust_preamble_top' o);
     to_sexp (rust_preamble_program' o);
     to_sexp (rust_term_box_symbol' o);
     to_sexp (rust_type_box_symbol' o);
     to_sexp (rust_any_type_symbol' o);
     to_sexp (rust_print_full_names' o);
     to_sexp (rust_default_attributes' o)
    ]%sexp.

Instance Serialize_elm_config : Serialize elm_config :=
  fun o =>
    [Atom "elm_config";
     to_sexp (elm_preamble o);
     to_sexp (elm_module_name o);
     to_sexp (elm_term_box_symbol o);
     to_sexp (elm_type_box_symbol o);
     to_sexp (elm_any_type_symbol o);
     to_sexp (elm_false_elim_def o);
     to_sexp (elm_print_full_names o)
    ]%sexp.

Instance Serialize_elm_config' : Serialize elm_config' :=
  fun o =>
    [Atom "elm_config";
     to_sexp (elm_preamble' o);
     to_sexp (elm_module_name' o);
     to_sexp (elm_term_box_symbol' o);
     to_sexp (elm_type_box_symbol' o);
     to_sexp (elm_any_type_symbol' o);
     to_sexp (elm_false_elim_def' o);
     to_sexp (elm_print_full_names' o)
    ]%sexp.

Instance Serialize_certicoq_config : Serialize certicoq_config :=
  fun o =>
    [Atom "certicoq_config";
     to_sexp (direct o);
     to_sexp (c_args o);
     to_sexp (o_level o);
     to_sexp (prefix o);
     to_sexp (body_name o)
    ]%sexp.

Instance Serialize_certicoq_config' : Serialize certicoq_config' :=
  fun o =>
    [Atom "certicoq_config";
     to_sexp (direct' o);
     to_sexp (c_args' o);
     to_sexp (o_level' o);
     to_sexp (prefix' o);
     to_sexp (body_name' o)
    ]%sexp.

Instance Serialize_program_type : Serialize Serialize.program_type :=
  fun n =>
    match n with
    | Serialize.Standalone => Atom "Standalone"
    | Serialize.Shared_lib m r => [ Atom "Shared_lib"; to_sexp m; to_sexp r ]
    end%sexp.

Instance Serialize_ocaml_config : Serialize ocaml_config :=
  fun o =>
    [Atom "ocaml_config";
     to_sexp (program_type o)
    ]%sexp.

Instance Serialize_ocaml_config' : Serialize ocaml_config' :=
  fun o =>
    [Atom "ocaml_config";
     to_sexp (program_type' o)
    ]%sexp.

Instance Serialize_cakeml_config : Serialize cakeml_config :=
  fun o =>
    @to_sexp _ Serialize_unit o.

Instance Serialize_cakeml_config' : Serialize cakeml_config' :=
  fun o =>
    @to_sexp _ Serialize_unit o.

Instance Serialize_backend_config : Serialize backend_config :=
  fun b =>
    match b with
    | Rust o => [Atom "Rust"; to_sexp o ]
    | Elm o => [Atom "Elm"; to_sexp o ]
    | C o => [Atom "C"; to_sexp o ]
    | Wasm o => [Atom "Wasm"; to_sexp o ]
    | OCaml o => [Atom "OCaml"; to_sexp o ]
    | CakeML o => [Atom "CakeML"; to_sexp o ]
    end%sexp.

Instance Serialize_backend_config' : Serialize backend_config' :=
  fun b =>
    match b with
    | Rust' o => [Atom "Rust"; to_sexp o ]
    | Elm' o => [Atom "Elm"; to_sexp o ]
    | C' o => [Atom "C"; to_sexp o ]
    | Wasm' o => [Atom "Wasm"; to_sexp o ]
    | OCaml' o => [Atom "OCaml"; to_sexp o ]
    | CakeML' o => [Atom "CakeML"; to_sexp o ]
    end%sexp.



(** ** Config Serializers *)

Instance Serialize_remapped_inductive : Serialize remapped_inductive :=
  fun o =>
    [Atom "remapped_inductive";
     to_sexp (re_ind_name o);
     to_sexp (re_ind_ctors o);
     to_sexp (re_ind_match o)
    ]%sexp.

Instance Serialize_external_remapping : Serialize external_remapping :=
  fun r =>
    to_sexp r.

Instance Serialize_inductive_mapping : Serialize EProgram.inductive_mapping :=
  fun r =>
    let '(kn, (s, n)) := r in
    [Atom "inductive_mapping";
     to_sexp kn;
     to_sexp s;
     to_sexp n
    ]%sexp.

Instance Serialize_remapping : Serialize remapping :=
  fun r =>
    match r with
    | RemapInductive kn er ri => [Atom "RemapInductive"; to_sexp kn; to_sexp er; to_sexp ri ]
    | RemapConstant kn er a gc s => [Atom "RemapConstant"; to_sexp kn; to_sexp er; to_sexp a; to_sexp gc; to_sexp s ]
    | RemapInlineConstant kn er a gc s => [Atom "RemapInlineConstant"; to_sexp kn; to_sexp er; to_sexp a; to_sexp gc; to_sexp s ]
    end%sexp.

Instance Serialize_custom_attribute : Serialize custom_attribute :=
  fun o =>
    to_sexp o.

Instance Serialize_inlinings : Serialize inlinings :=
  fun o =>
    to_sexp o.

Instance Serialize_remappings : Serialize remappings :=
  fun o =>
    to_sexp o.

Instance Serialize_custom_attributes : Serialize custom_attributes :=
  fun o =>
    to_sexp o.

Instance Serialize_erasure_phases : Serialize erasure_phases :=
  fun o =>
    [Atom "erasure_phases";
     to_sexp (implement_box o);
     to_sexp (implement_lazy o);
     to_sexp (cofix_to_laxy o);
     to_sexp (betared o);
     to_sexp (unboxing o);
     to_sexp (dearg_ctors o);
     to_sexp (dearg_consts o)
    ]%sexp.

Instance Serialize_erasure_phases' : Serialize erasure_phases' :=
  fun o =>
    [Atom "erasure_phases";
     to_sexp (implement_box' o);
     to_sexp (implement_lazy' o);
     to_sexp (cofix_to_laxy' o);
     to_sexp (betared' o);
     to_sexp (unboxing' o);
     to_sexp (dearg_ctors' o);
     to_sexp (dearg_consts' o)
    ]%sexp.

Instance Serialize_config : Serialize config :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts o);
     to_sexp (erasure_opts o);
     to_sexp (inlinings_opts o);
     to_sexp (remappings_opts o);
     to_sexp (cstr_reorders_opts o);
     to_sexp (custom_attributes_opts o)
    ]%sexp.

Instance Serialize_config' : Serialize config' :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts' o);
     to_sexp (erasure_opts' o);
     to_sexp (inlinings_opts' o);
     to_sexp (remappings_opts' o);
     to_sexp (cstr_reorders_opts' o);
     to_sexp (custom_attributes_opts' o)
    ]%sexp.

Instance Serialize_attributes_config : Serialize attributes_config :=
  fun o =>
    [Atom "attributes_config";
     to_sexp (inlinings_opt o);
     to_sexp (remappings_opt o);
     to_sexp (cstr_reorders_opt o);
     to_sexp (custom_attributes_opt o)
    ]%sexp.



(** * Deserializers *)

(** ** Backend Config *)

Instance Deserialize_rust_config : Deserialize rust_config :=
  fun l e =>
    Deser.match_con "rust_config" []
      [ ("rust_config", con7_ Build_rust_config) ]
      l e.

Instance Deserialize_rust_config' : Deserialize rust_config' :=
  fun l e =>
    Deser.match_con "rust_config" []
      [ ("rust_config", con7_ Build_rust_config') ]
      l e.

Instance Deserialize_elm_config : Deserialize elm_config :=
  fun l e =>
    Deser.match_con "elm_config" []
      [ ("elm_config", con7_ Build_elm_config) ]
      l e.

Instance Deserialize_elm_config' : Deserialize elm_config' :=
  fun l e =>
    Deser.match_con "elm_config" []
      [ ("elm_config", con7_ Build_elm_config') ]
      l e.

Instance Deserialize_certicoq_config : Deserialize certicoq_config :=
  fun l e =>
    Deser.match_con "certicoq_config" []
      [ ("certicoq_config", con5_ Build_certicoq_config) ]
      l e.

Instance Deserialize_certicoq_config' : Deserialize certicoq_config' :=
  fun l e =>
    Deser.match_con "certicoq_config" []
      [ ("certicoq_config", con5_ Build_certicoq_config') ]
      l e.

Instance Deserialize_program_type : Deserialize Serialize.program_type :=
  fun l e =>
    Deser.match_con "program_type"
      [ ("Standalone", Serialize.Standalone) ]
      [ ("Shared_lib", con2_ Serialize.Shared_lib) ]
      l e.

Instance Deserialize_ocaml_config : Deserialize ocaml_config :=
  fun l e =>
    Deser.match_con "ocaml_config" []
      [ ("ocaml_config", con1_ Build_ocaml_config) ]
      l e.

Instance Deserialize_ocaml_config' : Deserialize ocaml_config' :=
  fun l e =>
    Deser.match_con "ocaml_config" []
      [ ("ocaml_config", con1_ Build_ocaml_config') ]
      l e.

Instance Deserialize_cakeml_config : Deserialize cakeml_config :=
  fun l e =>
    @_from_sexp _ Deserialize_unit l e.

Instance Deserialize_cakeml_config' : Deserialize cakeml_config' :=
  fun l e =>
    @_from_sexp _ Deserialize_unit l e.

Instance Deserialize_backend_config : Deserialize backend_config :=
  fun l e =>
    Deser.match_con "backend_config" []
      [ ("Rust", Deser.con_ Rust);
        ("Elm", Deser.con_ Elm);
        ("C", Deser.con_ C);
        ("Wasm", Deser.con_ Wasm);
        ("OCaml", Deser.con_ OCaml);
        ("CakeML", Deser.con_ CakeML)
      ]
      l e.

Instance Deserialize_backend_config' : Deserialize backend_config' :=
  fun l e =>
    Deser.match_con "backend_config" []
      [ ("Rust", Deser.con_ Rust');
        ("Elm", Deser.con_ Elm');
        ("C", Deser.con_ C');
        ("Wasm", Deser.con_ Wasm');
        ("OCaml", Deser.con_ OCaml');
        ("CakeML", Deser.con_ CakeML')
      ]
      l e.



(** ** Config *)

Instance Deserialize_remapped_inductive : Deserialize remapped_inductive :=
  fun l e =>
    Deser.match_con "remapped_inductive" []
      [ ("remapped_inductive", con3_ build_remapped_inductive) ]
      l e.

Instance Deserialize_external_remapping : Deserialize external_remapping :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_inductive_mapping : Deserialize EProgram.inductive_mapping :=
  fun l e =>
    Deser.match_con "inductive_mapping" []
      [ ("inductive_mapping", con3_ (fun kn s n => (kn, (s, n)))) ]
      l e.

Instance Deserialize_remapping : Deserialize remapping :=
  fun l e =>
    Deser.match_con "remapping" []
      [ ("RemapInductive", con3_ RemapInductive);
        ("RemapConstant", con5_ RemapConstant);
        ("RemapInlineConstant", con5_ RemapInlineConstant)
      ]
      l e.

Instance Deserialize_custom_attribute : Deserialize custom_attribute :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_inlinings : Deserialize inlinings :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_remappings : Deserialize remappings :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_custom_attributes : Deserialize custom_attributes :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_erasure_phases : Deserialize erasure_phases :=
  fun l e =>
    Deser.match_con "erasure_phases" []
      [ ("erasure_phases", con7_ Build_erasure_phases) ]
      l e.

Instance Deserialize_erasure_phases' : Deserialize erasure_phases' :=
  fun l e =>
    Deser.match_con "erasure_phases" []
      [ ("erasure_phases", con7_ Build_erasure_phases') ]
      l e.

Instance Deserialize_config : Deserialize config :=
  fun l e =>
    Deser.match_con "config" []
      [ ("config", con6_ Build_config) ]
      l e.

Instance Deserialize_config' : Deserialize config' :=
  fun l e =>
    Deser.match_con "config" []
      [ ("config", con6_ Build_config') ]
      l e.

Instance Deserialize_attributes_config : Deserialize attributes_config :=
  fun l e =>
    Deser.match_con "attributes_config" []
      [ ("attributes_config", con4_ Build_attributes_config) ]
      l e.



(** * Main serialization functions *)

(** ** Backend Config *)

Definition string_of_rust_config (x : rust_config) : string :=
  @to_string rust_config Serialize_rust_config x.

Definition string_of_rust_config' (x : rust_config') : string :=
  @to_string rust_config' Serialize_rust_config' x.

Definition string_of_elm_config (x : elm_config) : string :=
  @to_string elm_config Serialize_elm_config x.

Definition string_of_elm_config' (x : elm_config') : string :=
  @to_string elm_config' Serialize_elm_config' x.

Definition string_of_certicoq_config (x : certicoq_config) : string :=
  @to_string certicoq_config Serialize_certicoq_config x.

Definition string_of_certicoq_config' (x : certicoq_config') : string :=
  @to_string certicoq_config' Serialize_certicoq_config' x.

Definition string_of_program_type (x : Serialize.program_type) : string :=
  @to_string Serialize.program_type Serialize_program_type x.

Definition string_of_ocaml_config (x : ocaml_config) : string :=
  @to_string ocaml_config Serialize_ocaml_config x.

Definition string_of_ocaml_config' (x : ocaml_config') : string :=
  @to_string ocaml_config' Serialize_ocaml_config' x.

Definition string_of_cakeml_config (x : cakeml_config) : string :=
  @to_string cakeml_config Serialize_cakeml_config x.

Definition string_of_cakeml_config' (x : cakeml_config') : string :=
  @to_string cakeml_config' Serialize_cakeml_config' x.

Definition string_of_backend_config (x : backend_config) : string :=
  @to_string backend_config Serialize_backend_config x.

Definition string_of_backend_config' (x : backend_config') : string :=
  @to_string backend_config' Serialize_backend_config' x.



(** ** Config *)

Definition string_of_remapped_inductive (x : remapped_inductive) : string :=
  @to_string remapped_inductive Serialize_remapped_inductive x.

Definition string_of_external_remapping (x : external_remapping) : string :=
  @to_string external_remapping Serialize_external_remapping x.

Definition string_of_inductive_mapping (x : inductive_mapping) : string :=
  @to_string inductive_mapping Serialize_inductive_mapping x.

Definition string_of_remapping (x : remapping) : string :=
  @to_string remapping Serialize_remapping x.

Definition string_of_custom_attribute (x : custom_attribute) : string :=
  @to_string custom_attribute Serialize_custom_attribute x.

Definition string_of_inlinings (x : inlinings) : string :=
  @to_string inlinings Serialize_inlinings x.

Definition string_of_remappings (x : remappings) : string :=
  @to_string remappings Serialize_remappings x.

Definition string_of_custom_attributes (x : custom_attributes) : string :=
  @to_string custom_attributes Serialize_custom_attributes x.

Definition string_of_erasure_phases (x : erasure_phases) : string :=
  @to_string erasure_phases Serialize_erasure_phases x.

Definition string_of_erasure_phases' (x : erasure_phases') : string :=
  @to_string erasure_phases' Serialize_erasure_phases' x.

Definition string_of_config (x : config) : string :=
  @to_string config Serialize_config x.

Definition string_of_config' (x : config') : string :=
  @to_string config' Serialize_config' x.

Definition string_of_attributes_config (x : attributes_config) : string :=
  @to_string attributes_config Serialize_attributes_config x.



(** * Main deserialization functions *)

(** ** Backend Config *)

Definition rust_config_of_string (s : string) : error + rust_config :=
  @from_string rust_config Deserialize_rust_config s.

Definition rust_config'_of_string (s : string) : error + rust_config' :=
  @from_string rust_config' Deserialize_rust_config' s.

Definition elm_config_of_string (s : string) : error + elm_config :=
  @from_string elm_config Deserialize_elm_config s.

Definition elm_config'_of_string (s : string) : error + elm_config' :=
  @from_string elm_config' Deserialize_elm_config' s.

Definition certicoq_config_of_string (s : string) : error + certicoq_config :=
  @from_string certicoq_config Deserialize_certicoq_config s.

Definition certicoq_config'_of_string (s : string) : error + certicoq_config' :=
  @from_string certicoq_config' Deserialize_certicoq_config' s.

Definition program_type_of_string (s : string) : error + Serialize.program_type :=
  @from_string Serialize.program_type Deserialize_program_type s.

Definition ocaml_config_of_string (s : string) : error + ocaml_config :=
  @from_string ocaml_config Deserialize_ocaml_config s.

Definition ocaml_config'_of_string (s : string) : error + ocaml_config' :=
  @from_string ocaml_config' Deserialize_ocaml_config' s.

Definition cakeml_config_of_string (s : string) : error + cakeml_config :=
  @from_string cakeml_config Deserialize_cakeml_config s.

Definition cakeml_config'_of_string (s : string) : error + cakeml_config' :=
  @from_string cakeml_config' Deserialize_cakeml_config' s.

Definition backend_config_of_string (s : string) : error + backend_config :=
  @from_string backend_config Deserialize_backend_config s.

Definition backend_config'_of_string (s : string) : error + backend_config' :=
  @from_string backend_config' Deserialize_backend_config' s.



(** ** Config *)

Definition remapped_inductive_of_string (s : string) : error + remapped_inductive :=
  @from_string remapped_inductive Deserialize_remapped_inductive s.

Definition external_remapping_of_string (s : string) : error + external_remapping :=
  @from_string external_remapping Deserialize_external_remapping s.

Definition inductive_mapping_of_string (s : string) : error + inductive_mapping :=
  @from_string inductive_mapping Deserialize_inductive_mapping s.

Definition remapping_of_string (s : string) : error + remapping :=
  @from_string remapping Deserialize_remapping s.

Definition custom_attribute_of_string (s : string) : error + custom_attribute :=
  @from_string custom_attribute Deserialize_custom_attribute s.

Definition inlinings_of_string (s : string) : error + inlinings :=
  @from_string inlinings Deserialize_inlinings s.

Definition remappings_of_string (s : string) : error + remappings :=
  @from_string remappings Deserialize_remappings s.

Definition custom_attributes_of_string (s : string) : error + custom_attributes :=
  @from_string custom_attributes Deserialize_custom_attributes s.

Definition erasure_phases_of_string (s : string) : error + erasure_phases :=
  @from_string erasure_phases Deserialize_erasure_phases s.

Definition erasure_phases'_of_string (s : string) : error + erasure_phases' :=
  @from_string erasure_phases' Deserialize_erasure_phases' s.

Definition config_of_string (s : string) : error + config :=
  @from_string config Deserialize_config s.

Definition config'_of_string (s : string) : error + config' :=
  @from_string config' Deserialize_config' s.

Definition attributes_config_of_string (s : string) : error + attributes_config :=
  @from_string attributes_config Deserialize_attributes_config s.
