{-# LANGUAGE NamedFieldPuns, ImportQualifiedPost, DataKinds, OverloadedStrings, UnicodeSyntax #-}
-- | Convert Agda datatypes to λ□ inductive declarations
module Agda2Lambox.Compile.Inductive
  ( compileInductive
  ) where

import Control.Monad.Reader ( ask, liftIO )
import Control.Monad ( forM, when, unless, (>=>) )
import Data.Functor ((<&>))
import Data.Foldable ( toList )
import Data.List ( elemIndex )
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.List.NonEmpty qualified as NEL
import Data.Maybe ( isJust, listToMaybe, fromMaybe )
import Data.Traversable ( mapM )

import Agda.Syntax.Abstract.Name ( QName, qnameModule, qnameName )
import Agda.TypeChecking.Monad.Base hiding (None)
import Agda.TypeChecking.Monad.Env ( withCurrentModule )
import Agda.TypeChecking.Datatypes ( ConstructorInfo(..), getConstructorInfo, isDatatype )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope (telViewUpTo, piApplyM, teleArgs, telView, flattenTel)
import Agda.TypeChecking.Substitute (TelView, TelV(theTel), apply)
import Agda.Compiler.Backend ( getConstInfo, lookupMutualBlock, reportSDoc, AddContext (addContext), constructorForm)
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Common (Arg)
import Agda.Syntax.Internal
import Agda.Utils.Monad ( unlessM )

import Agda.Utils
import LambdaBox.Target
import Agda2Lambox.Compile.Utils
import Agda2Lambox.Compile.Monad
import Agda2Lambox.Compile.Type
import LambdaBox qualified as LBox

-- | Toplevel conversion from a datatype/record definition to a Lambdabox declaration.
compileInductive :: Target t -> Definition -> CompileM (Maybe (LBox.GlobalDecl t))
compileInductive t defn@Defn{defName} = do
  mutuals <- liftTCM $ dataOrRecDefMutuals defn

  reportSDoc "agda2lambox.compile.inductive" 5 $
    "Inductive mutuals:" <+> prettyTCM mutuals

  {- NOTE():
     if mutuals is []:
       the record/datatype isn't recursive
     if mutuals is [q]:
       then q == defName,
       the record/datatype is inductive/coinductive but not mutually-defined
     otherwise,
       the record/datatype is mutually defined with other things -}

  let items = fromMaybe (NEL.singleton defName) $ NEL.nonEmpty mutuals

  -- ensure that all mutuals get compiled, eventually
  mapM_ requireDef items

  {- also note that we assume the list of mutuals will be the same
     for every record/datatype in the list (especially the order),
     as we make the first item in the list responsible for compiling all of them. -}

  if defName /= NEL.head items then do
    liftIO $ putStrLn $ "Skipping " <> prettyShow defName
    pure Nothing

  else do
    defs <- liftTCM $ mapM getConstInfo items

    unless (all (isDataOrRecDef . theDef) defs) $
      genericError "Mutually-defined datatypes/records *and* functions not supported."

    bodies <- forM defs $ actuallyConvertInductive t

    return $ Just $ LBox.InductiveDecl $ LBox.MutualInductive
      { indFinite = LBox.Finite -- TODO()
      , indPars   = 0
      , indBodies = NEL.toList bodies
      }


data InductiveBundle = Bundle
  { indName :: QName
  , indType :: Type
  , indCons :: [QName]
  , indPars :: Int
  }

-- | Gather the shared information for compiling inductives.
getBundle :: Definition -> InductiveBundle
getBundle defn@Defn{defName, defType, theDef} =
  case theDef of
    Datatype{dataPars, dataCons} ->
      Bundle
        { indName = defName
        , indType = defType
        , indCons = dataCons
        , indPars = dataPars
        }
    Record{recPars} ->
      Bundle
        { indName = defName
        , indType = defType
        , indCons = [recCon theDef]
        , indPars = recPars
        }


actuallyConvertInductive :: ∀ t. Target t -> Definition -> CompileM (LBox.OneInductiveBody t)
actuallyConvertInductive t defn = do
  let Bundle{..} = getBundle defn

  params <- theTel <$> telViewUpTo indPars indType

  reportSDoc "agda2lambox.compile.inductive" 10 $
    "Inductive parameters:" <+> prettyTCM params

  let pvars :: [Arg Term] = teleArgs params

  addContext params do

    tyvars <- whenTyped t $ forM (flattenTel params) \pdom -> do
      let domType = unDom pdom
      isParamLogical <- liftTCM $ isLogical pdom
      isParamArity   <- liftTCM $ isArity domType
      let isParamSort = isJust  $ isSort $ unEl domType
      pure LBox.TypeVarInfo
        { tvarName      = domToName pdom
        , tvarIsLogical = isParamLogical
        , tvarIsArity   = isParamArity
        , tvarIsSort    = isParamSort
        }

    ctors :: [LBox.ConstructorBody t] <-
      forM indCons \cname -> do
        arity <- liftTCM $ getConstructorInfo cname <&> \case
          DataCon arity         -> arity
          RecordCon _ _ arity _ -> arity

        conTypeInfo <- whenTyped t do
          conType <- liftTCM $ (`piApplyM` pvars) . defType =<< getConstInfo cname
          conTel  <- toList . theTel <$> telView conType
          compileArgs indPars conTel

        pure LBox.Constructor
          { cstrName  = qnameToIdent cname
          , cstrArgs  = arity
          , cstrTypes = conTypeInfo
          }

    pure LBox.OneInductive
      { indName          = qnameToIdent indName
      , indPropositional = False        -- TODO()
      , indKElim         = LBox.IntoAny -- TODO()
      , indCtors         = ctors
      , indProjs         = []
      , indTypeVars      = tyvars
      }
