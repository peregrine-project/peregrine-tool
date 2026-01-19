From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure Require Import EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
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
     to_sexp (rust_preamble o);
     to_sexp (rust_term_box_symbol o);
     to_sexp (rust_type_box_symbol o);
     to_sexp (rust_any_type_symbol o);
     to_sexp (rust_print_full_names o)
    ]%sexp.

Instance Serialize_rust_config' : Serialize rust_config' :=
  fun o =>
    [Atom "rust_config";
     to_sexp (rust_preamble' o);
     to_sexp (rust_term_box_symbol' o);
     to_sexp (rust_type_box_symbol' o);
     to_sexp (rust_any_type_symbol' o);
     to_sexp (rust_print_full_names' o)
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

Instance Serialize_backend_config : Serialize backend_config :=
  fun b =>
    match b with
    | Rust o => [Atom "Rust"; to_sexp o ]
    | Elm o => [Atom "Elm"; to_sexp o ]
    | C o => [Atom "C"; to_sexp o ]
    | Wasm o => [Atom "Wasm"; to_sexp o ]
    | OCaml o => [Atom "OCaml"; to_sexp o ]
    end%sexp.

Instance Serialize_backend_config' : Serialize backend_config' :=
  fun b =>
    match b with
    | Rust' o => [Atom "Rust"; to_sexp o ]
    | Elm' o => [Atom "Elm"; to_sexp o ]
    | C' o => [Atom "C"; to_sexp o ]
    | Wasm' o => [Atom "Wasm"; to_sexp o ]
    | OCaml' o => [Atom "OCaml"; to_sexp o ]
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
    | ReorderInductive im => [Atom "ReorderInductive"; to_sexp im ]
    | RemapConstant kn er s => [Atom "RemapConstant"; to_sexp kn; to_sexp er; to_sexp s ]
    | RemapInlineConstant kn er s => [Atom "RemapInlineConstant"; to_sexp kn; to_sexp er; to_sexp s ]
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
     to_sexp (dearg o);
     to_sexp (implement_box o);
     to_sexp (implement_lazy o);
     to_sexp (cofix_to_laxy o);
     to_sexp (betared o);
     to_sexp (inlining o);
     to_sexp (unboxing o)
    ]%sexp.

Instance Serialize_erasure_config : Serialize erasure_config :=
  fun o =>
    [Atom "erasure_config";
     to_sexp (phases o);
     to_sexp (dearging_do_trim_const_masks o);
     to_sexp (dearging_do_trim_ctor_masks o)
    ]%sexp.

Instance Serialize_erasure_config' : Serialize erasure_config' :=
  fun o =>
    [Atom "erasure_config";
     to_sexp (phases' o);
     to_sexp (dearging_do_trim_const_masks' o);
     to_sexp (dearging_do_trim_ctor_masks' o)
    ]%sexp.

Instance Serialize_config : Serialize config :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts o);
     to_sexp (erasure_opts o);
     to_sexp (inlinings_opts o);
     to_sexp (remappings_opts o);
     to_sexp (custom_attributes_opts o)
    ]%sexp.

Instance Serialize_config' : Serialize config' :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts' o);
     to_sexp (erasure_opts' o);
     to_sexp (inlinings_opts' o);
     to_sexp (remappings_opts' o);
     to_sexp (custom_attributes_opts' o)
    ]%sexp.
