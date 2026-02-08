-- Lambda Box configuration type definitions
-- Most fields are marked as optional, if set to Nothing
-- then the default value will be used
module LambdaBox.Config where

import qualified LambdaBox.LambdaBox



-- Rust backend configuration
data RustConfig = RustConfig
  { rustPreambleTop       :: Maybe String,
    rustPreambleProgram   :: Maybe String,
    rustTermBoxSymbol     :: Maybe String,
    rustTypeBoxSymbol     :: Maybe String,
    rustAnyTypeSyymbol    :: Maybe String,
    rustPrintFullNames    :: Maybe Bool,
    rustDefaultAttributes :: Maybe String
  }

-- Elm backend configuration
data ElmConfig = ElmConfig
  { elmPreamble       :: Maybe String,
    elmModuleName     :: Maybe String,
    elmTermBoxSymbol  :: Maybe String,
    elmTypeBoxSymbol  :: Maybe String,
    elmAnyTypeSyymbol :: Maybe String,
    elmFalseElimDef   :: Maybe String,
    elmPrintFullNames :: Maybe Bool
  }

-- CertiCoq (C & Webassembly) backend configuration
data CertiCoqConfig = CertiCoqConfig
  { direct    :: Maybe Bool,
    cArgs     :: Maybe Int,
    oLevel    :: Maybe Int,
    prefix    :: Maybe String,
    bodyName  :: Maybe String
  }

-- OCaml backend configuration
data ProgramType
  = Standalone
  --Reference to a plugin registration function
  | SharedLib String String

data OCamlConfig = OCamlConfig
  { programType :: Maybe ProgramType
  }

-- Backend configuration
-- States the backend that Peregrine should use along
-- with with options specific to that backend 
data BackendConfig
  = Rust RustConfig
  | Elm ElmConfig
  | C CertiCoqConfig
  | Wasm CertiCoqConfig
  | OCaml OCamlConfig



-- Inductive remapping
data RemappedInductive = RemappedInductive
  { indName   :: String,
    indCtors  :: [String],
    indMatch  :: Maybe String
  }

-- Remapping annotations
type ExternalRemapping = Maybe String
type Arity = Maybe Int

data Remapping
  = RemapInductive LambdaBox.LambdaBox.Inductive ExternalRemapping RemappedInductive
  | RemapConstant LambdaBox.LambdaBox.KerName ExternalRemapping Arity Bool String
  | RemapInlineConstant LambdaBox.LambdaBox.KerName ExternalRemapping Arity Bool String

type Remappings = [Remapping]

-- Constructor reorder annotations
type InductiveMapping = (LambdaBox.LambdaBox.Inductive, (String, [Int]))
type InductivesMapping = [InductiveMapping]

-- Inlining annotations
type Inlinings = [LambdaBox.LambdaBox.KerName]

-- Custom attributes
type CustomAttributes = [(LambdaBox.LambdaBox.KerName, String)]

-- Configure optional compilation phases
data ErasurePhases = ErasurePhases
  { implementBox  :: Maybe Bool,
    implementLaxy :: Maybe Bool,
    cofixToLazy   :: Maybe Bool,
    betared       :: Maybe Bool,
    unboxing      :: Maybe Bool,
    deargCtor     :: Maybe Bool,
    deargConst    :: Maybe Bool
  }

-- Configuration of Peregrine
data Config = Config
  { backendOpts       :: BackendConfig,
    erasureOpts       :: Maybe ErasurePhases,
    inlinings         :: Inlinings,
    remappings        :: Remappings,
    cstrReorders      :: InductivesMapping,
    customAttributes  :: CustomAttributes
  }
