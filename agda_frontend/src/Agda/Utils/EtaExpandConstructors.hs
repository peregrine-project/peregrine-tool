-- | Eta-expansion on constructors to fully-apply them, for treeless syntax.
module Agda.Utils.EtaExpandConstructors (etaExpandConstructors) where

import Data.Bifunctor (second)

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Datatypes
import Agda.Compiler.Treeless.Subst () --instance only
import Agda.Compiler.Backend
import Control.Monad.IO.Class (MonadIO(liftIO))


-- | Check whether a treeless term is a constructor applied to (many) terms.
unSpineCon :: TTerm -> Maybe (QName, [TTerm])
unSpineCon (TCon q)   = Just (q, [])
unSpineCon (TApp u v) = second (++ v) <$> unSpineCon u
unSpineCon _          = Nothing

-- | Return the arity of a constructor
getConArity :: ConstructorInfo -> Int
getConArity (DataCon a) = a
getConArity (RecordCon _ _ a _) = a

-- | Eta-expand treeless constructors.
etaExpandConstructors :: TTerm -> TCM TTerm
etaExpandConstructors t | Just (q, args) <- unSpineCon t = do
  arity <- getConArity <$> getConstructorInfo q
  let nargs = length args

  if nargs >= arity then -- should really be (==), but just in case
    TApp (TCon q) <$> mapM etaExpandConstructors args

  else do
    let nlam = arity - nargs
    exargs <- mapM (etaExpandConstructors . raise nlam) args
    let vars = TVar <$> reverse [0 .. nlam - 1]
    pure $ iterate TLam (TApp (TCon q) $ exargs ++ vars) !! nlam

etaExpandConstructors t = case t of
  TApp u v             -> TApp <$> etaExpandConstructors u <*> mapM etaExpandConstructors v
  TLam u               -> TLam <$> etaExpandConstructors u
  TLet u v             -> TLet <$> etaExpandConstructors u <*> etaExpandConstructors v
  TCase k ci tdef alts -> TCase k ci <$> etaExpandConstructors tdef
                                     <*> mapM etaExpandAlt alts
  TCoerce u            -> TCoerce <$> etaExpandConstructors u
  _                    -> pure t

etaExpandAlt :: TAlt -> TCM TAlt
etaExpandAlt = \case
  TACon q a b -> TACon q a <$> etaExpandConstructors b
  TAGuard a b -> TAGuard a <$> etaExpandConstructors b
  TALit l b   -> TALit l   <$> etaExpandConstructors b
