module Nat0 where

import qualified Prelude
import qualified Datatypes

add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (add p m)}

