{-# LANGUAGE OverloadedStrings #-}
-- | Definitions for λ□ identifiers, names and references.
module LambdaBox.Names where

import Agda.Syntax.Abstract.Name ( ModuleName(..), QName(..) )
import Agda.Syntax.Common.Pretty
import LambdaBox.LambdaBox

instance Pretty ModPath where
  pretty = \case
    MPFile  dp      -> cat $ punctuate "." (map pretty dp)
    MPBound dp id i -> "MPBound??" -- NOTE: don't know what this corresponds to
    MPDot mp i      -> pretty mp <> "." <> pretty i

instance Pretty KerName where
  pretty KerName{..} = pretty kerModPath <> "." <> text kerName

instance Pretty Inductive where
  pretty Inductive{..} = pretty indMInd <> braces (pretty indInd)

instance Pretty Name where
  pretty = \case
    Anon    -> "_"
    Named i -> text i
