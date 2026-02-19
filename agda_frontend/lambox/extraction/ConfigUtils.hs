module ConfigUtils where

import qualified Prelude
import qualified Config0
import qualified Datatypes
import qualified EProgram
import qualified Serialize
import qualified Bytestring

data Coq_rust_config' =
   Build_rust_config' (Prelude.Maybe Bytestring.String__Coq_t) (Prelude.Maybe
                                                               Bytestring.String__Coq_t) 
 (Prelude.Maybe Bytestring.String__Coq_t) (Prelude.Maybe
                                          Bytestring.String__Coq_t) (Prelude.Maybe
                                                                    Bytestring.String__Coq_t) 
 (Prelude.Maybe Prelude.Bool) (Prelude.Maybe Bytestring.String__Coq_t)

rust_preamble_top' :: Coq_rust_config' -> Prelude.Maybe
                      Bytestring.String__Coq_t
rust_preamble_top' r =
  case r of {
   Build_rust_config' rust_preamble_top'0 _ _ _ _ _ _ -> rust_preamble_top'0}

rust_preamble_program' :: Coq_rust_config' -> Prelude.Maybe
                          Bytestring.String__Coq_t
rust_preamble_program' r =
  case r of {
   Build_rust_config' _ rust_preamble_program'0 _ _ _ _ _ ->
    rust_preamble_program'0}

rust_term_box_symbol' :: Coq_rust_config' -> Prelude.Maybe
                         Bytestring.String__Coq_t
rust_term_box_symbol' r =
  case r of {
   Build_rust_config' _ _ rust_term_box_symbol'0 _ _ _ _ ->
    rust_term_box_symbol'0}

rust_type_box_symbol' :: Coq_rust_config' -> Prelude.Maybe
                         Bytestring.String__Coq_t
rust_type_box_symbol' r =
  case r of {
   Build_rust_config' _ _ _ rust_type_box_symbol'0 _ _ _ ->
    rust_type_box_symbol'0}

rust_any_type_symbol' :: Coq_rust_config' -> Prelude.Maybe
                         Bytestring.String__Coq_t
rust_any_type_symbol' r =
  case r of {
   Build_rust_config' _ _ _ _ rust_any_type_symbol'0 _ _ ->
    rust_any_type_symbol'0}

rust_print_full_names' :: Coq_rust_config' -> Prelude.Maybe Prelude.Bool
rust_print_full_names' r =
  case r of {
   Build_rust_config' _ _ _ _ _ rust_print_full_names'0 _ ->
    rust_print_full_names'0}

rust_default_attributes' :: Coq_rust_config' -> Prelude.Maybe
                            Bytestring.String__Coq_t
rust_default_attributes' r =
  case r of {
   Build_rust_config' _ _ _ _ _ _ rust_default_attributes'0 ->
    rust_default_attributes'0}

data Coq_elm_config' =
   Build_elm_config' (Prelude.Maybe Bytestring.String__Coq_t) (Prelude.Maybe
                                                              Bytestring.String__Coq_t) 
 (Prelude.Maybe Bytestring.String__Coq_t) (Prelude.Maybe
                                          Bytestring.String__Coq_t) (Prelude.Maybe
                                                                    Bytestring.String__Coq_t) 
 (Prelude.Maybe Bytestring.String__Coq_t) (Prelude.Maybe Prelude.Bool)

elm_preamble' :: Coq_elm_config' -> Prelude.Maybe Bytestring.String__Coq_t
elm_preamble' e =
  case e of {
   Build_elm_config' elm_preamble'0 _ _ _ _ _ _ -> elm_preamble'0}

elm_module_name' :: Coq_elm_config' -> Prelude.Maybe Bytestring.String__Coq_t
elm_module_name' e =
  case e of {
   Build_elm_config' _ elm_module_name'0 _ _ _ _ _ -> elm_module_name'0}

elm_term_box_symbol' :: Coq_elm_config' -> Prelude.Maybe
                        Bytestring.String__Coq_t
elm_term_box_symbol' e =
  case e of {
   Build_elm_config' _ _ elm_term_box_symbol'0 _ _ _ _ ->
    elm_term_box_symbol'0}

elm_type_box_symbol' :: Coq_elm_config' -> Prelude.Maybe
                        Bytestring.String__Coq_t
elm_type_box_symbol' e =
  case e of {
   Build_elm_config' _ _ _ elm_type_box_symbol'0 _ _ _ ->
    elm_type_box_symbol'0}

elm_any_type_symbol' :: Coq_elm_config' -> Prelude.Maybe
                        Bytestring.String__Coq_t
elm_any_type_symbol' e =
  case e of {
   Build_elm_config' _ _ _ _ elm_any_type_symbol'0 _ _ ->
    elm_any_type_symbol'0}

elm_false_elim_def' :: Coq_elm_config' -> Prelude.Maybe
                       Bytestring.String__Coq_t
elm_false_elim_def' e =
  case e of {
   Build_elm_config' _ _ _ _ _ elm_false_elim_def'0 _ -> elm_false_elim_def'0}

elm_print_full_names' :: Coq_elm_config' -> Prelude.Maybe Prelude.Bool
elm_print_full_names' e =
  case e of {
   Build_elm_config' _ _ _ _ _ _ elm_print_full_names'0 ->
    elm_print_full_names'0}

data Coq_certicoq_config' =
   Build_certicoq_config' (Prelude.Maybe Prelude.Bool) (Prelude.Maybe
                                                       Datatypes.Coq_nat) 
 (Prelude.Maybe Datatypes.Coq_nat) (Prelude.Maybe Bytestring.String__Coq_t) 
 (Prelude.Maybe Bytestring.String__Coq_t)

direct' :: Coq_certicoq_config' -> Prelude.Maybe Prelude.Bool
direct' c =
  case c of {
   Build_certicoq_config' direct'0 _ _ _ _ -> direct'0}

c_args' :: Coq_certicoq_config' -> Prelude.Maybe Datatypes.Coq_nat
c_args' c =
  case c of {
   Build_certicoq_config' _ c_args'0 _ _ _ -> c_args'0}

o_level' :: Coq_certicoq_config' -> Prelude.Maybe Datatypes.Coq_nat
o_level' c =
  case c of {
   Build_certicoq_config' _ _ o_level'0 _ _ -> o_level'0}

prefix' :: Coq_certicoq_config' -> Prelude.Maybe Bytestring.String__Coq_t
prefix' c =
  case c of {
   Build_certicoq_config' _ _ _ prefix'0 _ -> prefix'0}

body_name' :: Coq_certicoq_config' -> Prelude.Maybe Bytestring.String__Coq_t
body_name' c =
  case c of {
   Build_certicoq_config' _ _ _ _ body_name'0 -> body_name'0}

type Coq_c_config' = Coq_certicoq_config'

type Coq_wasm_config' = Coq_certicoq_config'

type Coq_ocaml_config' =
  Prelude.Maybe Serialize.Coq_program_type
  -- singleton inductive, whose constructor was Build_ocaml_config'
  
program_type' :: Coq_ocaml_config' -> Prelude.Maybe
                 Serialize.Coq_program_type
program_type' o =
  o

type Coq_cakeml_config' = ()

data Coq_backend_config' =
   Rust' Coq_rust_config'
 | Elm' Coq_elm_config'
 | C' Coq_c_config'
 | Wasm' Coq_wasm_config'
 | OCaml' Coq_ocaml_config'
 | CakeML' Coq_cakeml_config'

data Coq_erasure_phases' =
   Build_erasure_phases' (Prelude.Maybe Prelude.Bool) (Prelude.Maybe
                                                      Prelude.Bool) (Prelude.Maybe
                                                                    Prelude.Bool) 
 (Prelude.Maybe Prelude.Bool) (Prelude.Maybe Prelude.Bool) (Prelude.Maybe
                                                           Prelude.Bool) 
 (Prelude.Maybe Prelude.Bool)

implement_box' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
implement_box' e =
  case e of {
   Build_erasure_phases' implement_box'0 _ _ _ _ _ _ -> implement_box'0}

implement_lazy' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
implement_lazy' e =
  case e of {
   Build_erasure_phases' _ implement_lazy'0 _ _ _ _ _ -> implement_lazy'0}

cofix_to_laxy' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
cofix_to_laxy' e =
  case e of {
   Build_erasure_phases' _ _ cofix_to_laxy'0 _ _ _ _ -> cofix_to_laxy'0}

betared' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
betared' e =
  case e of {
   Build_erasure_phases' _ _ _ betared'0 _ _ _ -> betared'0}

unboxing' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
unboxing' e =
  case e of {
   Build_erasure_phases' _ _ _ _ unboxing'0 _ _ -> unboxing'0}

dearg_ctors' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
dearg_ctors' e =
  case e of {
   Build_erasure_phases' _ _ _ _ _ dearg_ctors'0 _ -> dearg_ctors'0}

dearg_consts' :: Coq_erasure_phases' -> Prelude.Maybe Prelude.Bool
dearg_consts' e =
  case e of {
   Build_erasure_phases' _ _ _ _ _ _ dearg_consts'0 -> dearg_consts'0}

data Coq_config' =
   Build_config' Coq_backend_config' (Prelude.Maybe Coq_erasure_phases') 
 Config0.Coq_inlinings Config0.Coq_constant_remappings Config0.Coq_inductive_remappings 
 EProgram.Coq_inductives_mapping Config0.Coq_custom_attributes

backend_opts' :: Coq_config' -> Coq_backend_config'
backend_opts' c =
  case c of {
   Build_config' backend_opts'0 _ _ _ _ _ _ -> backend_opts'0}

erasure_opts' :: Coq_config' -> Prelude.Maybe Coq_erasure_phases'
erasure_opts' c =
  case c of {
   Build_config' _ erasure_opts'0 _ _ _ _ _ -> erasure_opts'0}

inlinings_opts' :: Coq_config' -> Config0.Coq_inlinings
inlinings_opts' c =
  case c of {
   Build_config' _ _ inlinings_opts'0 _ _ _ _ -> inlinings_opts'0}

const_remappings_opts' :: Coq_config' -> Config0.Coq_constant_remappings
const_remappings_opts' c =
  case c of {
   Build_config' _ _ _ const_remappings_opts'0 _ _ _ ->
    const_remappings_opts'0}

ind_remappings_opts' :: Coq_config' -> Config0.Coq_inductive_remappings
ind_remappings_opts' c =
  case c of {
   Build_config' _ _ _ _ ind_remappings_opts'0 _ _ -> ind_remappings_opts'0}

cstr_reorders_opts' :: Coq_config' -> EProgram.Coq_inductives_mapping
cstr_reorders_opts' c =
  case c of {
   Build_config' _ _ _ _ _ cstr_reorders_opts'0 _ -> cstr_reorders_opts'0}

custom_attributes_opts' :: Coq_config' -> Config0.Coq_custom_attributes
custom_attributes_opts' c =
  case c of {
   Build_config' _ _ _ _ _ _ custom_attributes_opts'0 ->
    custom_attributes_opts'0}

