{-# LANGUAGE OverloadedStrings, DataKinds, GADTs #-}
-- | Haskell encoding of the LambdaBox syntax.
module LambdaBox
  ( module LambdaBox.Names
  , module LambdaBox.Term
  , module LambdaBox.Type
  , module LambdaBox.Env
  , module LambdaBox.LambdaBox
  , emptyName
  , emptyDecl
  ) where

import Control.Monad.Identity
import LambdaBox.Target
import LambdaBox.Names
import LambdaBox.Term
import LambdaBox.Type
import LambdaBox.Env
import LambdaBox.LambdaBox

-- | Kername for the backed-in empty type.
emptyName :: KerName
emptyName = KerName (MPFile ["LamBox"]) "Empty"

-- | Backed-in definition for the empty type.
--   Used to discard unreachable branches in typed targets.
emptyDecl :: Target t -> GlobalDecl t
emptyDecl t = InductiveDecl MutualInductive
  { indFinite = Finite
  , indPars   = 0
  , indBodies = [
      OneInductive
        { indName          = "Empty"
        , indPropositional = False
        , indKElim         = IntoAny
        , indTypeVars      = runIdentity $ whenTyped t $ pure []
        , indCtors         = []
        , indProjs         = []
        }
    ]
  }
