module LambdaBox.ConfigConvert where

import LambdaBox.LBoxConvert (inductiveConv, kerNameConv, natConv, stringConv)
import LambdaBox.Config
import qualified Config0
import qualified ConfigUtils
import qualified EProgram
import qualified Serialize



-- Rust backend configuration
rustConfigConv :: RustConfig -> ConfigUtils.Coq_rust_config'
rustConfigConv RustConfig {..} =
  ConfigUtils.Build_rust_config'
    (fmap stringConv rustPreambleTop)
    (fmap stringConv rustPreambleProgram)
    (fmap stringConv rustTermBoxSymbol)
    (fmap stringConv rustTypeBoxSymbol)
    (fmap stringConv rustAnyTypeSyymbol)
    rustPrintFullNames
    (fmap stringConv rustDefaultAttributes)

-- Elm backend configuration
elmConfigConv :: ElmConfig -> ConfigUtils.Coq_elm_config'
elmConfigConv ElmConfig {..} =
  ConfigUtils.Build_elm_config'
    (fmap stringConv elmPreamble)
    (fmap stringConv elmModuleName)
    (fmap stringConv elmTermBoxSymbol)
    (fmap stringConv elmTypeBoxSymbol)
    (fmap stringConv elmAnyTypeSyymbol)
    (fmap stringConv elmFalseElimDef)
    elmPrintFullNames

-- CertiCoq (C & Webassembly) backend configuration
certicoqConfigConv :: CertiCoqConfig -> ConfigUtils.Coq_certicoq_config'
certicoqConfigConv CertiCoqConfig {..} =
  ConfigUtils.Build_certicoq_config'
    direct
    (fmap natConv cArgs)
    (fmap natConv oLevel)
    (fmap stringConv prefix)
    (fmap stringConv bodyName)

-- OCaml backend configuration
programTypeConv :: ProgramType -> Serialize.Coq_program_type
programTypeConv Standalone = Serialize.Standalone
programTypeConv (SharedLib s1 s2) =
  Serialize.Shared_lib (stringConv s1) (stringConv s2)

ocamlConfigConv :: OCamlConfig -> ConfigUtils.Coq_ocaml_config'
ocamlConfigConv OCamlConfig {..} =
  fmap programTypeConv programType

-- Backend configuration
backendConfigConv :: BackendConfig -> ConfigUtils.Coq_backend_config'
backendConfigConv (Rust c) = ConfigUtils.Rust' $ rustConfigConv c
backendConfigConv (Elm c) = ConfigUtils.Elm' $ elmConfigConv c
backendConfigConv (C c) = ConfigUtils.C' $ certicoqConfigConv c
backendConfigConv (Wasm c) = ConfigUtils.Wasm' $ certicoqConfigConv c
backendConfigConv (OCaml c) = ConfigUtils.OCaml' $ ocamlConfigConv c

-- Inductive remapping
remappedInductiveConv :: RemappedInductive -> Config0.Coq_remapped_inductive
remappedInductiveConv RemappedInductive {..} =
  Config0.Coq_build_remapped_inductive
    (stringConv indName)
    (map stringConv indCtors)
    (fmap stringConv indMatch)

-- Remapping annotations
externalRemappingConv :: ExternalRemapping -> Config0.Coq_external_remapping
externalRemappingConv r =
  fmap stringConv r

arityConv :: Arity -> Config0.Coq_arity
arityConv i =
  fmap natConv i

remappingConv :: Remapping -> Config0.Coq_remapping
remappingConv (RemapInductive ind ext r) =
  Config0.RemapInductive
    (inductiveConv ind)
    (externalRemappingConv ext)
    (remappedInductiveConv r)
remappingConv (RemapConstant kn ext a gc s) =
  Config0.RemapConstant
    (kerNameConv kn)
    (externalRemappingConv ext)
    (arityConv a)
    gc
    (stringConv s)
remappingConv (RemapInlineConstant kn ext a gc s) =
  Config0.RemapInlineConstant
    (kerNameConv kn)
    (externalRemappingConv ext)
    (arityConv a)
    gc
    (stringConv s)

remappingsConv :: Remappings -> Config0.Coq_remappings
remappingsConv l = map remappingConv l

-- Constructor reorder annotations
inductiveMappingConv :: InductiveMapping -> EProgram.Coq_inductive_mapping
inductiveMappingConv (ind, (s, is)) =
  (inductiveConv ind, (stringConv s, map natConv is))

inductivesMappingConv :: InductivesMapping -> EProgram.Coq_inductives_mapping
inductivesMappingConv l = map inductiveMappingConv l

-- Inlining annotations
inliningsConv :: Inlinings -> Config0.Coq_inlinings
inliningsConv l = map kerNameConv l

-- Custom attributes
customAttributesConv :: CustomAttributes -> Config0.Coq_custom_attributes
customAttributesConv l =
  map (\x -> (kerNameConv $ fst x, stringConv $ snd x)) l

-- Configure optional compilation phases
erasurePhasesConv :: ErasurePhases -> ConfigUtils.Coq_erasure_phases'
erasurePhasesConv ErasurePhases {..} =
  ConfigUtils.Build_erasure_phases'
    implementBox
    implementLaxy
    cofixToLazy
    betared
    unboxing
    deargCtor
    deargConst

-- Configuration of Peregrine
configConv :: Config -> ConfigUtils.Coq_config'
configConv Config {..} =
  ConfigUtils.Build_config'
    (backendConfigConv backendOpts)
    (fmap erasurePhasesConv erasureOpts)
    (inliningsConv inlinings)
    (remappingsConv remappings)
    (inductivesMappingConv cstrReorders)
    (customAttributesConv customAttributes)
