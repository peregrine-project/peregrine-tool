module BinNums where

import qualified Prelude

data Coq_positive =
   Coq_xI Coq_positive
 | Coq_xO Coq_positive
 | Coq_xH

data N =
   N0
 | Npos Coq_positive

data Z =
   Z0
 | Zpos Coq_positive
 | Zneg Coq_positive

