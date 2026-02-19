module BasicAst where

import qualified Prelude
import qualified Kernames

data Coq_name =
   Coq_nAnon
 | Coq_nNamed Kernames.Coq_ident

data Coq_recursivity_kind =
   Finite
 | CoFinite
 | BiFinite

