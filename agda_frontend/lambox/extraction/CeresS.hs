module CeresS where

import qualified Prelude
import qualified BinNums
import qualified Bytestring

data Coq_sexp_ a =
   Atom_ a
 | List (([]) (Coq_sexp_ a))

data Coq_atom =
   Num BinNums.Z
 | Str Bytestring.String__Coq_t
 | Raw Bytestring.String__Coq_t

