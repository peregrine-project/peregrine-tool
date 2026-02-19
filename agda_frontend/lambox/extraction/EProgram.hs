module EProgram where

import qualified Prelude
import qualified Datatypes
import qualified Kernames
import qualified Bytestring

type Coq_inductive_mapping =
  (,) Kernames.Coq_inductive
  ((,) Bytestring.String__Coq_t (([]) Datatypes.Coq_nat))

type Coq_inductives_mapping = ([]) Coq_inductive_mapping

