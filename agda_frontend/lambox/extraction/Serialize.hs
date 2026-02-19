module Serialize where

import qualified Prelude
import qualified Bytestring

data Coq_program_type =
   Standalone
 | Shared_lib Bytestring.String__Coq_t Bytestring.String__Coq_t

