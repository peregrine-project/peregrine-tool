{-# LANGUAGE DerivingVia, GeneralizedNewtypeDeriving, OverloadedStrings, DeriveFunctor, DeriveTraversable, NamedFieldPuns #-}
-- | Compilation monad.
module Agda2Lambox.Compile.Monad
  ( CompileM
  , CompileEnv(..)
  , requireDef
  , runCompile
  , compileLoop
  , genericError
  , genericDocError
  , internalError
  , CompiledItem(..)
  , ask
  , asks
  ) where

import Control.Monad ( unless )
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.IO.Class ( MonadIO )
import Data.Bifunctor ( bimap )
import Data.Set ( Set )
import Data.Set qualified as Set
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.Maybe ( catMaybes )

import Agda.Syntax.Abstract (QName)
import Agda.Compiler.Backend (getConstInfo, PureTCM, HasConstInfo, HasBuiltins, canonicalName)
import Agda.TypeChecking.Monad (MonadDebug, MonadTrace, MonadAddContext)
import Agda.TypeChecking.Monad.Debug (MonadDebug, reportSDoc)
import Agda.TypeChecking.Monad.Base hiding (initState)
import Agda.Utils.List ( mcons )
import Agda.Utils.Monad ( unlessM )
import Agda.TypeChecking.Pretty
import Control.Monad.Error.Class (MonadError)

import Data.Foldable (traverse_)

-- | Compilation Environment
data CompileEnv = CompileEnv
  { blocks :: Bool
      -- ^ When set to 'False', constructors take no arguments,
      -- and regular function application is used instead.
  }

-- | Backend compilation state.
data CompileState = CompileState
  { seenDefs     :: Set QName
    -- ^ Names that we have seen, either already compiled or in the stack.
  , compileStack :: [QName]
    -- ^ Compilation stack.
  , requiredDefs :: Set QName
    -- ^ (Locally) required definitions.
  }

-- Initial compile state.
initState :: CompileState
initState = CompileState
  { seenDefs     = Set.empty
  , compileStack = []
  , requiredDefs = Set.empty
  }

-- | Backend compilation monad.
newtype CompileM a = Compile (ReaderT CompileEnv (StateT CompileState TCM) a)
  deriving newtype (Functor, Applicative, Monad)
  deriving newtype (MonadIO, MonadFail, MonadDebug, ReadTCState, MonadTrace)
  deriving newtype (MonadError TCErr, MonadTCEnv, MonadTCState, HasOptions, MonadTCM)
  deriving newtype (MonadAddContext, MonadReduce, HasConstInfo, HasBuiltins, PureTCM)
  deriving newtype (MonadReader CompileEnv)

-- | Require a definition to be compiled.
requireDef :: QName -> CompileM ()
requireDef q = Compile $ do
  q <- liftTCM $ canonicalName q

  -- add name to the required list
  modify \ s -> s { requiredDefs = Set.insert q (requiredDefs s) }

  seen <- gets seenDefs

  -- a name is only added to the queue if we haven't seen it yet
  unless (Set.member q seen) do

    reportSDoc "agda2lambox.compile.require" 10 $
      "Requiring definition:" <+> prettyTCM q

    modify \ s -> s
      { seenDefs     = Set.insert q seen
      , compileStack = q : compileStack s
      }

-- | Get the next qname to be compiled, if there is one.
nextUnit :: CompileM (Maybe QName)
nextUnit = Compile $
  gets compileStack >>= \case
    []   -> pure Nothing
    q:qs -> Just q <$ modify \ s -> s {compileStack = qs}


-- | Record the required definitions of a compilation unit.
trackDeps :: CompileM a -> CompileM (a, [QName])
trackDeps (Compile c) = Compile do
  modify \s -> s {requiredDefs = Set.empty}
  x <- c
  deps <- gets requiredDefs
  pure (x, Set.toList deps)

-- | Run a compile action in 'TCM'.
runCompile :: CompileEnv -> CompileM a -> TCM a
runCompile env (Compile c) = evalStateT (runReaderT c env) initState

-- | Run the processing function as long as there are names to be compiled.
--  Returns a list of compiled items, (topologically) sorted by dependency order.
--  This means that whenever @A@ depends on @B@, @A@ will appear before @B@ in the list.
compileLoop
  :: forall a. (Definition -> CompileM (Maybe a))
             -- ^ The compilation function
  -> [QName] -- ^ Initial names to compile
  -> CompileM [CompiledItem a]
compileLoop step names = do
  traverse_ requireDef names
  topoSort <$> loop
  where
  loop :: CompileM [CompiledItem (Maybe a)]
  loop@(Compile unloop) = nextUnit >>= \case
    Nothing -> pure []
    Just q  -> do
      (mr, deps) <- trackDeps . step =<< (liftTCM $ getConstInfo q)
      (CompiledItem q deps mr:) <$> loop


-- * Compilation items and topological sort

-- | Named compilation item, with a set of dependencies.
data CompiledItem a = CompiledItem
  { itemName  :: QName
  , itemDeps  :: [QName]
  , itemValue :: a
  } deriving (Functor, Foldable, Traversable)

-- | Stateful monad for the topological sort.
-- State contains the list of items that have been permanently inserted,
-- along with their names.
type TopoM a = State (Set QName, [CompiledItem a])

-- | Topological sort of compiled items, based on dependencies.
-- Skipped items are required for dependency analysis, as they
-- can transively force ordering
-- (e.g constructors are skipped but force compilation of their datatype).
-- In the end, we get a list of items that are effectively compiled.
topoSort :: forall a. [CompiledItem (Maybe a)] -> [CompiledItem a]
topoSort defs = snd $ execState (traverse (visit Set.empty) defs) (Set.empty, [])
  where
    items = Map.fromList $ map (\x -> (itemName x, x)) defs

    -- | Whether an item has been permanently inserted already
    isMarked :: QName -> TopoM a Bool
    isMarked q = Set.member q <$> gets fst

    push :: CompiledItem (Maybe a) -> TopoM a ()
    push item@CompiledItem{itemName, itemValue}
      | Just value <- itemValue
      = modify $ bimap (Set.insert itemName) (item {itemValue = value}:)
      | otherwise = pure ()

    visit :: Set QName -> CompiledItem (Maybe a) -> TopoM a ()
    visit temp item@CompiledItem{..} = do
      -- NOTE(): Visiting an item that has already been temporarily marked
      --  means something went wrong and we have a cycle in the graph.
      --  We could throw an error, but this should never happen.
      --  Here, we continue and pick an arbitrary order.
      unlessM ((Set.member itemName temp ||) <$> isMarked itemName) do
        let deps = catMaybes $ (`Map.lookup` items) <$> itemDeps
        traverse (visit (Set.insert itemName temp)) deps
        push item
