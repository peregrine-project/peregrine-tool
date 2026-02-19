module Config0 where

import qualified Prelude
import qualified Datatypes
import qualified EProgram
import qualified ERemapInductives
import qualified Kernames
import qualified Bytestring

data Coq_remapped_inductive =
   Coq_build_remapped_inductive Bytestring.String__Coq_t (([])
                                                         Bytestring.String__Coq_t) 
 (Prelude.Maybe Bytestring.String__Coq_t)

re_ind_name :: Coq_remapped_inductive -> Bytestring.String__Coq_t
re_ind_name r =
  case r of {
   Coq_build_remapped_inductive re_ind_name0 _ _ -> re_ind_name0}

re_ind_ctors :: Coq_remapped_inductive -> ([]) Bytestring.String__Coq_t
re_ind_ctors r =
  case r of {
   Coq_build_remapped_inductive _ re_ind_ctors0 _ -> re_ind_ctors0}

re_ind_match :: Coq_remapped_inductive -> Prelude.Maybe
                Bytestring.String__Coq_t
re_ind_match r =
  case r of {
   Coq_build_remapped_inductive _ _ re_ind_match0 -> re_ind_match0}

data Coq_remapped_constant =
   Build_remapped_constant (Prelude.Maybe Bytestring.String__Coq_t) Datatypes.Coq_nat 
 Prelude.Bool Prelude.Bool Bytestring.String__Coq_t

re_const_ext :: Coq_remapped_constant -> Prelude.Maybe
                Bytestring.String__Coq_t
re_const_ext r =
  case r of {
   Build_remapped_constant re_const_ext0 _ _ _ _ -> re_const_ext0}

re_const_arity :: Coq_remapped_constant -> Datatypes.Coq_nat
re_const_arity r =
  case r of {
   Build_remapped_constant _ re_const_arity0 _ _ _ -> re_const_arity0}

re_const_gc :: Coq_remapped_constant -> Prelude.Bool
re_const_gc r =
  case r of {
   Build_remapped_constant _ _ re_const_gc0 _ _ -> re_const_gc0}

re_const_inl :: Coq_remapped_constant -> Prelude.Bool
re_const_inl r =
  case r of {
   Build_remapped_constant _ _ _ re_const_inl0 _ -> re_const_inl0}

re_const_s :: Coq_remapped_constant -> Bytestring.String__Coq_t
re_const_s r =
  case r of {
   Build_remapped_constant _ _ _ _ re_const_s0 -> re_const_s0}

data Coq_remap_inductive =
   KnIndRemap ERemapInductives.Coq_extract_inductive
 | StringIndRemap Coq_remapped_inductive

type Coq_custom_attribute = (,) Kernames.Coq_kername Bytestring.String__Coq_t

type Coq_inlinings = ([]) Kernames.Coq_kername

type Coq_constant_remappings =
  ([]) ((,) Kernames.Coq_kername Coq_remapped_constant)

type Coq_inductive_remappings =
  ([]) ((,) Kernames.Coq_inductive Coq_remap_inductive)

type Coq_custom_attributes = ([]) Coq_custom_attribute

data Coq_attributes_config =
   Build_attributes_config Coq_inlinings Coq_constant_remappings Coq_inductive_remappings 
 EProgram.Coq_inductives_mapping Coq_custom_attributes

inlinings_opt :: Coq_attributes_config -> Coq_inlinings
inlinings_opt a =
  case a of {
   Build_attributes_config inlinings_opt0 _ _ _ _ -> inlinings_opt0}

const_remappings_opt :: Coq_attributes_config -> Coq_constant_remappings
const_remappings_opt a =
  case a of {
   Build_attributes_config _ const_remappings_opt0 _ _ _ ->
    const_remappings_opt0}

ind_remappings_opt :: Coq_attributes_config -> Coq_inductive_remappings
ind_remappings_opt a =
  case a of {
   Build_attributes_config _ _ ind_remappings_opt0 _ _ -> ind_remappings_opt0}

cstr_reorders_opt :: Coq_attributes_config -> EProgram.Coq_inductives_mapping
cstr_reorders_opt a =
  case a of {
   Build_attributes_config _ _ _ cstr_reorders_opt0 _ -> cstr_reorders_opt0}

custom_attributes_opt :: Coq_attributes_config -> Coq_custom_attributes
custom_attributes_opt a =
  case a of {
   Build_attributes_config _ _ _ _ custom_attributes_opt0 ->
    custom_attributes_opt0}

