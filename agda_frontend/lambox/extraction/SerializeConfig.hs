module SerializeConfig where

import qualified Prelude
import qualified CeresS
import qualified CeresSerialize
import qualified Config0
import qualified ConfigUtils
import qualified EProgram
import qualified ERemapInductives
import qualified Serialize
import qualified SerializeCommon
import qualified Bytestring

coq_Serialize_rust_config' :: CeresSerialize.Serialize
                              ConfigUtils.Coq_rust_config'
coq_Serialize_rust_config' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'r'
    (Bytestring.String__String 'u' (Bytestring.String__String 's'
    (Bytestring.String__String 't' (Bytestring.String__String '_'
    (Bytestring.String__String 'c' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 'f'
    (Bytestring.String__String 'i' (Bytestring.String__String 'g'
    Bytestring.String__EmptyString))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_preamble_top' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_preamble_program' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_term_box_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_type_box_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_any_type_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.rust_print_full_names' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.rust_default_attributes' o))
    ([])))))))))

coq_Serialize_elm_config' :: CeresSerialize.Serialize
                             ConfigUtils.Coq_elm_config'
coq_Serialize_elm_config' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'e'
    (Bytestring.String__String 'l' (Bytestring.String__String 'm'
    (Bytestring.String__String '_' (Bytestring.String__String 'c'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 'f' (Bytestring.String__String 'i'
    (Bytestring.String__String 'g' Bytestring.String__EmptyString))))))))))))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_preamble' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_module_name' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_term_box_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_type_box_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_any_type_symbol' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.elm_false_elim_def' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.elm_print_full_names' o))
    ([])))))))))

coq_Serialize_certicoq_config' :: CeresSerialize.Serialize
                                  ConfigUtils.Coq_certicoq_config'
coq_Serialize_certicoq_config' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'c'
    (Bytestring.String__String 'e' (Bytestring.String__String 'r'
    (Bytestring.String__String 't' (Bytestring.String__String 'i'
    (Bytestring.String__String 'c' (Bytestring.String__String 'o'
    (Bytestring.String__String 'q' (Bytestring.String__String '_'
    (Bytestring.String__String 'c' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 'f'
    (Bytestring.String__String 'i' (Bytestring.String__String 'g'
    Bytestring.String__EmptyString))))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.direct' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        (CeresSerialize.coq_Serialize_Integral
          CeresSerialize.coq_Integral_nat))
      (ConfigUtils.c_args' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        (CeresSerialize.coq_Serialize_Integral
          CeresSerialize.coq_Integral_nat))
      (ConfigUtils.o_level' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.prefix' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (ConfigUtils.body_name' o))
    ([])))))))

coq_Serialize_program_type :: CeresSerialize.Serialize
                              Serialize.Coq_program_type
coq_Serialize_program_type n =
  case n of {
   Serialize.Standalone -> CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'S' (Bytestring.String__String 't'
    (Bytestring.String__String 'a' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'a'
    (Bytestring.String__String 'l' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)))))))))));
   Serialize.Shared_lib m r -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'S' (Bytestring.String__String 'h'
    (Bytestring.String__String 'a' (Bytestring.String__String 'r'
    (Bytestring.String__String 'e' (Bytestring.String__String 'd'
    (Bytestring.String__String '_' (Bytestring.String__String 'l'
    (Bytestring.String__String 'i' (Bytestring.String__String 'b'
    Bytestring.String__EmptyString)))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident m) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident r) ([]))))}

coq_Serialize_ocaml_config' :: CeresSerialize.Serialize
                               ConfigUtils.Coq_ocaml_config'
coq_Serialize_ocaml_config' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'o'
    (Bytestring.String__String 'c' (Bytestring.String__String 'a'
    (Bytestring.String__String 'm' (Bytestring.String__String 'l'
    (Bytestring.String__String '_' (Bytestring.String__String 'c'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 'f' (Bytestring.String__String 'i'
    (Bytestring.String__String 'g'
    Bytestring.String__EmptyString)))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option coq_Serialize_program_type)
      (ConfigUtils.program_type' o))
    ([])))

coq_Serialize_cakeml_config' :: CeresSerialize.Serialize
                                ConfigUtils.Coq_cakeml_config'
coq_Serialize_cakeml_config' o =
  CeresSerialize.to_sexp CeresSerialize.coq_Serialize_unit o

coq_Serialize_backend_config' :: CeresSerialize.Serialize
                                 ConfigUtils.Coq_backend_config'
coq_Serialize_backend_config' b =
  case b of {
   ConfigUtils.Rust' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'R' (Bytestring.String__String 'u'
    (Bytestring.String__String 's' (Bytestring.String__String 't'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_rust_config' o) ([])));
   ConfigUtils.Elm' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'E' (Bytestring.String__String 'l'
    (Bytestring.String__String 'm' Bytestring.String__EmptyString))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_elm_config' o) ([])));
   ConfigUtils.C' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'C' Bytestring.String__EmptyString))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_certicoq_config' o) ([])));
   ConfigUtils.Wasm' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'W' (Bytestring.String__String 'a'
    (Bytestring.String__String 's' (Bytestring.String__String 'm'
    Bytestring.String__EmptyString)))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_certicoq_config' o) ([])));
   ConfigUtils.OCaml' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'O' (Bytestring.String__String 'C'
    (Bytestring.String__String 'a' (Bytestring.String__String 'm'
    (Bytestring.String__String 'l' Bytestring.String__EmptyString))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_ocaml_config' o) ([])));
   ConfigUtils.CakeML' o -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'C' (Bytestring.String__String 'a'
    (Bytestring.String__String 'k' (Bytestring.String__String 'e'
    (Bytestring.String__String 'M' (Bytestring.String__String 'L'
    Bytestring.String__EmptyString)))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_cakeml_config' o) ([])))}

coq_Serialize_remapped_inductive :: CeresSerialize.Serialize
                                    Config0.Coq_remapped_inductive
coq_Serialize_remapped_inductive o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'r'
    (Bytestring.String__String 'e' (Bytestring.String__String 'm'
    (Bytestring.String__String 'a' (Bytestring.String__String 'p'
    (Bytestring.String__String 'p' (Bytestring.String__String 'e'
    (Bytestring.String__String 'd' (Bytestring.String__String '_'
    (Bytestring.String__String 'i' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'u'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String 'i' (Bytestring.String__String 'v'
    (Bytestring.String__String 'e'
    Bytestring.String__EmptyString)))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident
      (Config0.re_ind_name o))
    ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_dirpath
      (Config0.re_ind_ctors o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (Config0.re_ind_match o))
    ([])))))

coq_Serialize_remapped_constant :: CeresSerialize.Serialize
                                   Config0.Coq_remapped_constant
coq_Serialize_remapped_constant o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'r'
    (Bytestring.String__String 'e' (Bytestring.String__String 'm'
    (Bytestring.String__String 'a' (Bytestring.String__String 'p'
    (Bytestring.String__String 'p' (Bytestring.String__String 'e'
    (Bytestring.String__String 'd' (Bytestring.String__String '_'
    (Bytestring.String__String 'c' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 's'
    (Bytestring.String__String 't' (Bytestring.String__String 'a'
    (Bytestring.String__String 'n' (Bytestring.String__String 't'
    Bytestring.String__EmptyString))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option
        SerializeCommon.coq_Serialize_ident)
      (Config0.re_const_ext o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_Integral CeresSerialize.coq_Integral_nat)
      (Config0.re_const_arity o))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (Config0.re_const_gc o))
    ((:)
    (CeresSerialize.to_sexp CeresSerialize.coq_Serialize_bool
      (Config0.re_const_inl o))
    ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident
      (Config0.re_const_s o))
    ([])))))))

coq_Serialize_inductive_mapping :: CeresSerialize.Serialize
                                   EProgram.Coq_inductive_mapping
coq_Serialize_inductive_mapping r =
  case r of {
   (,) kn p ->
    case p of {
     (,) s n -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
      (Bytestring.String__String 'i' (Bytestring.String__String 'n'
      (Bytestring.String__String 'd' (Bytestring.String__String 'u'
      (Bytestring.String__String 'c' (Bytestring.String__String 't'
      (Bytestring.String__String 'i' (Bytestring.String__String 'v'
      (Bytestring.String__String 'e' (Bytestring.String__String '_'
      (Bytestring.String__String 'm' (Bytestring.String__String 'a'
      (Bytestring.String__String 'p' (Bytestring.String__String 'p'
      (Bytestring.String__String 'i' (Bytestring.String__String 'n'
      (Bytestring.String__String 'g'
      Bytestring.String__EmptyString))))))))))))))))))) ((:)
      (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_inductive kn)
      ((:) (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_ident s)
      ((:)
      (CeresSerialize.to_sexp
        (CeresSerialize.coq_Serialize_list
          (CeresSerialize.coq_Serialize_Integral
            CeresSerialize.coq_Integral_nat))
        n)
      ([])))))}}

coq_Serialize_extract_inductive :: CeresSerialize.Serialize
                                   ERemapInductives.Coq_extract_inductive
coq_Serialize_extract_inductive r =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'e'
    (Bytestring.String__String 'x' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'a'
    (Bytestring.String__String 'c' (Bytestring.String__String 't'
    (Bytestring.String__String '_' (Bytestring.String__String 'i'
    (Bytestring.String__String 'n' (Bytestring.String__String 'd'
    (Bytestring.String__String 'u' (Bytestring.String__String 'c'
    (Bytestring.String__String 't' (Bytestring.String__String 'i'
    (Bytestring.String__String 'v' (Bytestring.String__String 'e'
    Bytestring.String__EmptyString))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list
        SerializeCommon.coq_Serialize_kername)
      (ERemapInductives.cstrs r))
    ((:)
    (CeresSerialize.to_sexp SerializeCommon.coq_Serialize_kername
      (ERemapInductives.elim r))
    ([]))))

coq_Serialize_remap_inductive :: CeresSerialize.Serialize
                                 Config0.Coq_remap_inductive
coq_Serialize_remap_inductive r =
  case r of {
   Config0.KnIndRemap r0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'K' (Bytestring.String__String 'n'
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'R'
    (Bytestring.String__String 'e' (Bytestring.String__String 'm'
    (Bytestring.String__String 'a' (Bytestring.String__String 'p'
    Bytestring.String__EmptyString)))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_extract_inductive r0) ([])));
   Config0.StringIndRemap r0 -> CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw
    (Bytestring.String__String 'S' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'i'
    (Bytestring.String__String 'n' (Bytestring.String__String 'g'
    (Bytestring.String__String 'I' (Bytestring.String__String 'n'
    (Bytestring.String__String 'd' (Bytestring.String__String 'R'
    (Bytestring.String__String 'e' (Bytestring.String__String 'm'
    (Bytestring.String__String 'a' (Bytestring.String__String 'p'
    Bytestring.String__EmptyString)))))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_remapped_inductive r0) ([])))}

coq_Serialize_custom_attribute :: CeresSerialize.Serialize
                                  Config0.Coq_custom_attribute
coq_Serialize_custom_attribute o =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_product
      SerializeCommon.coq_Serialize_kername
      SerializeCommon.coq_Serialize_ident)
    o

coq_Serialize_inlinings :: CeresSerialize.Serialize Config0.Coq_inlinings
coq_Serialize_inlinings o =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list SerializeCommon.coq_Serialize_kername)
    o

coq_Serialize_constant_remappings :: CeresSerialize.Serialize
                                     Config0.Coq_constant_remappings
coq_Serialize_constant_remappings o =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list
      (CeresSerialize.coq_Serialize_product
        SerializeCommon.coq_Serialize_kername
        coq_Serialize_remapped_constant))
    o

coq_Serialize_inductive_remappings :: CeresSerialize.Serialize
                                      Config0.Coq_inductive_remappings
coq_Serialize_inductive_remappings o =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list
      (CeresSerialize.coq_Serialize_product
        SerializeCommon.coq_Serialize_inductive
        coq_Serialize_remap_inductive))
    o

coq_Serialize_custom_attributes :: CeresSerialize.Serialize
                                   Config0.Coq_custom_attributes
coq_Serialize_custom_attributes o =
  CeresSerialize.to_sexp
    (CeresSerialize.coq_Serialize_list coq_Serialize_custom_attribute) o

coq_Serialize_erasure_phases' :: CeresSerialize.Serialize
                                 ConfigUtils.Coq_erasure_phases'
coq_Serialize_erasure_phases' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'e'
    (Bytestring.String__String 'r' (Bytestring.String__String 'a'
    (Bytestring.String__String 's' (Bytestring.String__String 'u'
    (Bytestring.String__String 'r' (Bytestring.String__String 'e'
    (Bytestring.String__String '_' (Bytestring.String__String 'p'
    (Bytestring.String__String 'h' (Bytestring.String__String 'a'
    (Bytestring.String__String 's' (Bytestring.String__String 'e'
    (Bytestring.String__String 's'
    Bytestring.String__EmptyString)))))))))))))))) ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.implement_box' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.implement_lazy' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.cofix_to_laxy' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.betared' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.unboxing' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.dearg_ctors' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option CeresSerialize.coq_Serialize_bool)
      (ConfigUtils.dearg_consts' o))
    ([])))))))))

coq_Serialize_config' :: CeresSerialize.Serialize ConfigUtils.Coq_config'
coq_Serialize_config' o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'c'
    (Bytestring.String__String 'o' (Bytestring.String__String 'n'
    (Bytestring.String__String 'f' (Bytestring.String__String 'i'
    (Bytestring.String__String 'g' Bytestring.String__EmptyString))))))))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_backend_config'
      (ConfigUtils.backend_opts' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_option coq_Serialize_erasure_phases')
      (ConfigUtils.erasure_opts' o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_inlinings
      (ConfigUtils.inlinings_opts' o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_constant_remappings
      (ConfigUtils.const_remappings_opts' o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_inductive_remappings
      (ConfigUtils.ind_remappings_opts' o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_inductive_mapping)
      (ConfigUtils.cstr_reorders_opts' o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_custom_attributes
      (ConfigUtils.custom_attributes_opts' o))
    ([])))))))))

coq_Serialize_attributes_config :: CeresSerialize.Serialize
                                   Config0.Coq_attributes_config
coq_Serialize_attributes_config o =
  CeresS.List ((:) (CeresS.Atom_ (CeresS.Raw (Bytestring.String__String 'a'
    (Bytestring.String__String 't' (Bytestring.String__String 't'
    (Bytestring.String__String 'r' (Bytestring.String__String 'i'
    (Bytestring.String__String 'b' (Bytestring.String__String 'u'
    (Bytestring.String__String 't' (Bytestring.String__String 'e'
    (Bytestring.String__String 's' (Bytestring.String__String '_'
    (Bytestring.String__String 'c' (Bytestring.String__String 'o'
    (Bytestring.String__String 'n' (Bytestring.String__String 'f'
    (Bytestring.String__String 'i' (Bytestring.String__String 'g'
    Bytestring.String__EmptyString))))))))))))))))))) ((:)
    (CeresSerialize.to_sexp coq_Serialize_inlinings
      (Config0.inlinings_opt o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_constant_remappings
      (Config0.const_remappings_opt o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_inductive_remappings
      (Config0.ind_remappings_opt o))
    ((:)
    (CeresSerialize.to_sexp
      (CeresSerialize.coq_Serialize_list coq_Serialize_inductive_mapping)
      (Config0.cstr_reorders_opt o))
    ((:)
    (CeresSerialize.to_sexp coq_Serialize_custom_attributes
      (Config0.custom_attributes_opt o))
    ([])))))))

string_of_backend_config' :: ConfigUtils.Coq_backend_config' ->
                             Bytestring.String__Coq_t
string_of_backend_config' x =
  CeresSerialize.to_string coq_Serialize_backend_config' x

string_of_erasure_phases' :: ConfigUtils.Coq_erasure_phases' ->
                             Bytestring.String__Coq_t
string_of_erasure_phases' x =
  CeresSerialize.to_string coq_Serialize_erasure_phases' x

string_of_config' :: ConfigUtils.Coq_config' -> Bytestring.String__Coq_t
string_of_config' x =
  CeresSerialize.to_string coq_Serialize_config' x

string_of_attributes_config :: Config0.Coq_attributes_config ->
                               Bytestring.String__Coq_t
string_of_attributes_config x =
  CeresSerialize.to_string coq_Serialize_attributes_config x

