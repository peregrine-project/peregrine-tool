{-# LANGUAGE NamedFieldPuns, DataKinds, OverloadedStrings #-}
-- | Convert Agda functions to λ□ constant declarations
module Agda2Lambox.Compile.Function
  ( compileFunction
  ) where

import Control.Monad ( forM, when, filterM, unless )
import Control.Monad.IO.Class ( liftIO )
import Data.List ( elemIndex )
import Data.Maybe ( isNothing, fromMaybe )

import Data.Foldable (toList)
import Agda.Syntax.Abstract.Name ( QName, qnameModule )
import Agda.TypeChecking.Monad.Base hiding ( None )
import Agda.TypeChecking.Pretty
import Agda.Compiler.Backend ( getConstInfo, funInline, reportSDoc )
import Agda.Syntax.Internal (domName)
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Common ( hasQuantityω )
import Agda.Utils.Monad (guardWithError, whenM)
import Agda.Utils.Lens ( (^.) )

import Agda.Utils ( treeless, pp, isRecordProjection, isArity )
import LambdaBox.Target
import Agda2Lambox.Compile.Utils
import Agda2Lambox.Compile.Monad
import Agda2Lambox.Compile.Term ( compileTerm )
import Agda2Lambox.Compile.Type ( compileTopLevelType, compileType )

import LambdaBox qualified as LBox
import LambdaBox.LambdaBox
import Agda.TypeChecking.Telescope (telViewUpTo)
import Agda.TypeChecking.Substitute (TelV(theCore, theTel))


-- | Check whether a definition is a function.
isFunction :: Definition -> Bool
isFunction Defn{..} | Function{} <- theDef = True
isFunction _ = False


-- | Convert a function body to a Lambdabox term.
compileFunctionBody :: [QName] -> Definition -> CompileM LBox.Term
compileFunctionBody ms Defn{defName, theDef} = do
  Just t <- liftTCM $ treeless defName

  reportSDoc "agda2lambox.compile.function" 10 $
    "treeless body:" <+> pretty t

  compileTerm ms t


-- | Whether to compile a function definition to λ□.
shouldCompileFunction :: Definition -> Bool
shouldCompileFunction def@Defn{theDef} | Function{..} <- theDef
  = not (theDef ^. funInline) -- not inlined (from module application)
    && isNothing funExtLam    -- not a pattern-lambda-generated function (inlined by the treeless translation)
    && isNothing funWith      -- not a with-generated function           (inlined by the treeless translation)
    && hasQuantityω def       -- non-erased

-- | Convert a function definition to a λ□ declaration.
compileFunction :: Target t -> Definition -> CompileM (Maybe (LBox.GlobalDecl t))
compileFunction t defn | not (shouldCompileFunction defn) = pure Nothing
compileFunction (t :: Target t) defn@Defn{defType} = do
  let fundef@Function{funMutual = Just mutuals} = theDef defn

  reportSDoc "agda2lambox.compile.function" 5 $
    "Function mutuals:" <+> prettyTCM mutuals

  defs <- liftTCM $ mapM getConstInfo mutuals

  unless (all isFunction defs) $
    genericError "Only mutually defined functions are supported."

  -- the mutual functions that we actually compile
  -- (so no with-generated functions, etc...)
  let mdefs  = filter shouldCompileFunction defs
  let mnames = map defName mdefs

  -- (conditionally) compile type of function
  typ <- whenTyped t $ case isRecordProjection fundef of
    Nothing -> compileTopLevelType defType

    -- if it is a (real) projection, drop the parameters from the type
    Just (recName, _) -> do
      Record{recPars} <- fmap theDef $ liftTCM $ getConstInfo recName
      projTel <- telViewUpTo recPars defType
      projType <- theCore <$> telViewUpTo recPars defType
      let names  = map domName $ toList $ theTel projTel
          pnames = map (maybe LBox.Anon (LBox.Named . sanitize . prettyShow)) names
      (pnames,) <$> compileType recPars projType

    -- TODO(): ^ take care of projection-like functions
    --                they should be eta-expanded somehow,
    --                OR treated like projections

  let builder :: LBox.Term -> Maybe (LBox.GlobalDecl t)
      builder = Just . ConstantDecl . ConstantBody typ . Just

  -- if the function is not recursive, just compile the body
  if null mdefs then builder <$> compileFunctionBody [] defn

  -- otherwise, take fixpoint
  else do
    let k = fromMaybe 0 $ elemIndex (defName defn) mnames

    builder . flip LBox.LFix k <$>
      forM mdefs \def@Defn{defName} -> do
        body <- compileFunctionBody mnames def >>= \case
          l@LBox.LLambda{} -> pure l
          LBox.LBox        -> pure $ LBox.LLambda LBox.Anon LBox.LBox
          _                -> genericError "Fixpoint body must be Lambda."
        return LBox.Def
          { dName = qnameToName defName
          , dBody = body
          , dArgs = 0
          }
