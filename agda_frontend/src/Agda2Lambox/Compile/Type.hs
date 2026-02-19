{-# LANGUAGE LambdaCase, FlexibleInstances, MultiWayIf, NamedFieldPuns #-}
module Agda2Lambox.Compile.Type where
--   ( compileType
--   , compileTopLevelType
--   , compileArgs
--   , getTypeVarInfo
--   ) where


import Control.Category ((>>>))
import Control.Monad.Reader
import Control.Monad ( mapM )
import Data.List ( foldl' )
import Data.Function ( (&) )
import Data.Bifunctor ( second )
import Data.Maybe ( isJust, mapMaybe )
import Data.Function ( applyWhen )

import Agda.Syntax.Common ( unArg, Arg (Arg) )
import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute ( absBody, TelV (theCore), absApp )
import Agda.TypeChecking.Telescope (telView)
import Agda.TypeChecking.Monad.Base ( TCM, MonadTCM (liftTCM), Definition(..))
import Agda.TypeChecking.Monad.Signature ( canonicalName )
import Agda.TypeChecking.Telescope ( mustBePi )
import Agda.Utils.Monad ( ifM )

import qualified LambdaBox as LBox
import Agda2Lambox.Compile.Utils
import Agda2Lambox.Compile.Monad
import Agda.Compiler.Backend (HasConstInfo(getConstInfo), Definition(Defn), AddContext (addContext))
import Agda.Utils (isDataOrRecDef, getInductiveParams, isArity, maybeUnfoldCopy)


-- | The kind of variables that are locally bound
data VarType = TypeVar Int | Other

-- | λ□ type compilation environment.
data TypeEnv = TypeEnv
  { typeVars   :: Int
    -- ^ How many type variables we have.
  , boundVars  :: Int
    -- ^ Amount of bound variables (including type variables)
  , boundTypes :: [VarType]
    -- ^ Information about the type variables in question.
    -- Should be indexed using de Bruijn indices.
  , insertVars :: Bool
    -- ^ Whether new type variables can be inserted
  }

-- | Initialize compilation environment with a given number of type variables.
initEnv :: Int -> TypeEnv
initEnv tvs = TypeEnv
  { typeVars   = tvs
  , boundVars  = tvs
  , boundTypes = reverse $ TypeVar <$> [0 .. tvs - 1]
  , insertVars = True
  }

runC :: Int -> C a -> CompileM a
runC tvs m = runReaderT m (initEnv tvs)

runCNoVars :: Int -> C a -> CompileM a
runCNoVars tvs m = runReaderT m ((initEnv tvs) { insertVars = False })

-- | Increment the number of locally-bound variables.
--   Extend the context with the given type info.
--   The new variable is always considered 'Other'.
underBinder :: Dom Type -> C a -> C a
underBinder v = addContext v . local \e -> e
  { boundVars  = boundVars e + 1
  , boundTypes = Other : boundTypes e
  }

-- | Increment the number of locally-bound variables.
--   Tries to insert a new type variable, if it's allowed.
underTypeVar :: Dom Type -> C a -> C a
underTypeVar b x = do
  shouldInsert <- asks insertVars
  if shouldInsert then
    addContext b $ local (\e@TypeEnv{..} -> e
      { typeVars   = typeVars + 1
      , boundVars  = boundVars + 1
      , boundTypes = TypeVar typeVars : boundTypes
      }) x
  else underBinder b x

-- | Type compilation monad.
type C a = ReaderT TypeEnv CompileM a


-- | Compile constructor arguments' types, given a set number of type variables.
compileArgs :: Int -> [Dom Type] -> CompileM [(LBox.Name, LBox.Type)]
compileArgs tvars = runC tvars . compileArgsC
  where
  compileArgsC :: [Dom Type] -> C [(LBox.Name, LBox.Type)]
  compileArgsC [] = pure []
  compileArgsC (dom:args) = do
    let name = domToName dom
    typ <- ifM (liftTCM $ isLogical dom) (pure LBox.TBox) (compileTypeC $ unDom dom)
    ((name, typ):) <$> underBinder dom (compileArgsC args)


-- | Compile a top-level type to λ□, lifting out type variables.
-- See [Extracting functional programs from Coq, in Coq](https://arxiv.org/pdf/2108.02995).
compileTopLevelType :: Type -> CompileM ([LBox.Name], LBox.Type)
compileTopLevelType = runC 0 . compileTopLevelTypeC

-- | Compile a type, given a number of type variables in scope.
--   Will not introduce more type variables.
compileType :: Int -> Type -> CompileM LBox.Type
compileType tvars = runC tvars . compileTypeC

compileTypeC :: Type -> C LBox.Type
compileTypeC = local (\e -> e { insertVars = False }) . fmap snd . compileTopLevelTypeC

compileElims :: Type -> Args -> C [LBox.Type]
compileElims _ [] = pure []
compileElims ty (x:xs) = do
  (a, b) <- mustBePi ty
  rest   <- compileElims (absApp b $ unArg x) xs
  first  <- ifM (liftTCM $ isLogical a)
              (pure LBox.TBox)
              (fmap snd $ compileTypeTerm $ unArg x)
  pure (first : rest)

getTypeVarInfo :: Dom Type -> TCM LBox.TypeVarInfo
getTypeVarInfo typ = do
  let theTyp = unDom typ
  isLg <- isLogical theTyp
  isAr <- isArity theTyp
  let isSt = isJust $ isSort $ unEl theTyp
  pure LBox.TypeVarInfo
    { tvarName      = domToName typ
    , tvarIsArity   = isAr
    , tvarIsLogical = isLg
    , tvarIsSort    = isSt
    }


compileTopLevelTypeC :: Type -> C ([LBox.Name], LBox.Type)
compileTopLevelTypeC typ =
  ifM (liftTCM $ isLogical typ) (pure ([], LBox.TBox)) $
    compileTypeTerm (unEl typ)

-- NOTE():
--   More or less the algorithm described in the paper (E^T in Fig.2).
compileTypeTerm :: Term -> C ([LBox.Name], LBox.Type)
compileTypeTerm = \case
  Sort{}     -> pure ([], LBox.TBox)
  Level{}    -> pure ([], LBox.TBox)
  DontCare{} -> pure ([], LBox.TBox)

  Var n _ -> do
    -- NOTE(): I think we should distinguish b/w "other" and logical variables
    (!! n) <$> asks boundTypes >>= \case
      TypeVar n -> pure ([], LBox.TVar n)
      Other     -> pure ([], LBox.TAny  )

  Def q es -> maybeUnfoldCopy q es compileTypeTerm \q es -> do
    Defn{theDef = def, defType, defArgInfo, defName} <- liftTCM $ getConstInfo q

    isLogicalDef <- liftTCM $ isLogical $ Arg defArgInfo defType

    -- if this def is logical, we ignore it (and its arguments)
    if isLogicalDef then pure ([], LBox.TBox)

    -- if it's an inductive, we only apply the parameters
    else if isDataOrRecDef def then do
      lift $ requireDef q
      ind <- liftTCM $ toInductive q
      let args = mapMaybe isApplyElim es
      ([],) . foldl' LBox.TApp (LBox.TInd ind)
        <$> compileElims defType (take (getInductiveParams def) args)

    -- otherwise, it must have been compiled as a type scheme,
    -- and therefore is kept with all arguments.

    -- TODO(): check whether indeed the fallback is always compiled to a typescheme.
    --              what about non-logical defs that are not arities or w/?
    -- TODO(): possibly merge the logic with the above for datatypes
    else do
      q <- liftTCM $ canonicalName q
      lift $ requireDef q
      let ts = qnameToKName q
      let args = mapMaybe isApplyElim es
      ([],) . foldl' LBox.TApp (LBox.TConst ts)
        <$> compileElims defType args

  Pi dom codom -> do
    let domType   = unDom dom
    let codomType = absBody codom

    domIsLogical <- liftTCM $ isLogical dom
    domIsArity   <- liftTCM $ isArity domType

    -- logical types and non-arities can never be lifted to type variables,
    -- so we keep going
    if domIsLogical || not domIsArity then do
      domType' <- if domIsLogical then pure LBox.TBox
                                  else compileTypeC domType
      (vars, codomType') <- underBinder dom $ compileTopLevelTypeC codomType
      pure (vars, LBox.TArr domType' codomType')

    else do
      (vars, codomType') <- underTypeVar dom $ compileTopLevelTypeC codomType
      let name = domToName dom
      pure (name : vars, LBox.TArr LBox.TBox codomType')

  _ -> pure ([], LBox.TAny)
