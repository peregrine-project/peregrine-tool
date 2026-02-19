{-
NOTE():
Taken straight from Agda source.
There are two important differences:
- we also add branches for unreachable defaults (because we need all cases to be exhaustive)
- we sort the case alts according to the order of constructors for the given inductive
-}

-- | Eliminates case defaults by adding an alternative for all possible
-- constructors. Literal cases are preserved as-is.
module Agda.Utils.EliminateDefaults where

import Control.Monad
import qualified Data.List as List
import Control.Monad.IO.Class (liftIO)

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst () -- instance only


eliminateCaseDefaults :: TTerm -> TCM TTerm
eliminateCaseDefaults = tr
  where
    tr :: TTerm -> TCM TTerm
    tr = \case
      TCase sc ct@CaseInfo{caseType = CTData qn} def alts -> do
        dtCons <- defConstructors . theDef <$> getConstInfo qn

        let missingCons = dtCons List.\\ map aCon alts
        def <- tr def

        -- we produce a new alternative for every missing constructor
        -- whose body is the default body, raised by #args brought in scope
        newAlts <- forM missingCons \con -> do
          Constructor {conArity = ar} <- theDef <$> getConstInfo con
          return $ TACon con ar $ raise ar def

        alts' <- (++ newAlts) <$> mapM trAlt alts

        -- then we sort the alts
        let alts'' = flip List.sortOn alts' \alt -> List.elemIndex (aCon alt) dtCons

        return $ TCase sc ct tUnreachable alts''

      -- case on non-data are always exhaustive
      TCase sc ct def alts -> TCase sc ct <$> tr def <*> mapM trAlt alts

      TCoerce a -> TCoerce <$> tr a
      TLam b    -> TLam <$> tr b
      TApp a bs -> TApp <$> tr a <*> mapM tr bs
      TLet e b  -> TLet <$> tr e <*> tr b

      t -> return t

    trAlt :: TAlt -> TCM TAlt
    trAlt = \case
      TAGuard g b -> TAGuard <$> tr g <*> tr b
      TACon q a b -> TACon q a <$> tr b
      TALit l b   -> TALit l <$> tr b
