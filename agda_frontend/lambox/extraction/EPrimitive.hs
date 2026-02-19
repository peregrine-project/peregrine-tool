module EPrimitive where

import qualified Prelude
import qualified PrimFloat
import qualified PrimInt63
import qualified PrimString
import qualified Primitive
import qualified Specif

data Coq_array_model term =
   Build_array_model term (([]) term)

array_default :: (Coq_array_model a1) -> a1
array_default a =
  case a of {
   Build_array_model array_default0 _ -> array_default0}

array_value :: (Coq_array_model a1) -> ([]) a1
array_value a =
  case a of {
   Build_array_model _ array_value0 -> array_value0}

data Coq_prim_model term =
   Coq_primIntModel PrimInt63.Coq_int
 | Coq_primFloatModel PrimFloat.Coq_float
 | Coq_primStringModel PrimString.Coq_string
 | Coq_primArrayModel (Coq_array_model term)

type Coq_prim_val term =
  Specif.Coq_sigT Primitive.Coq_prim_tag (Coq_prim_model term)

prim_val_tag :: (Coq_prim_val a1) -> Primitive.Coq_prim_tag
prim_val_tag =
  Specif.projT1

prim_val_model :: (Coq_prim_val a1) -> Coq_prim_model a1
prim_val_model =
  Specif.projT2

