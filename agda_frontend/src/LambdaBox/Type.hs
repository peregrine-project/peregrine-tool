{-# LANGUAGE OverloadedStrings #-}
-- | Definition of λ□ types.
module LambdaBox.Type where

import Agda.Syntax.Common.Pretty
import LambdaBox.Names
import LambdaBox.LambdaBox

instance Pretty Type where
  prettyPrec p = \case
    TBox         -> "□"
    TAny         -> "𝕋"
    TArr s t     -> mparens (p > 0) $ prettyPrec 1 s <+> "→" <+> pretty t
    TApp s t     -> mparens (p > 9) $ pretty s <+> prettyPrec 10 t
    TVar n       -> "@" <> pretty n
    TInd ind     -> mparens (p > 0) $ pretty ind
    TConst kname -> pretty kname
