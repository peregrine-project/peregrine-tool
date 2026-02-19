module Specif where

import qualified Prelude

data Coq_sigT a p =
   Coq_existT a p

projT1 :: (Coq_sigT a1 a2) -> a1
projT1 x =
  case x of {
   Coq_existT a _ -> a}

projT2 :: (Coq_sigT a1 a2) -> a2
projT2 x =
  case x of {
   Coq_existT _ h -> h}

