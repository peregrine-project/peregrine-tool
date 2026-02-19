module BinInt where

import qualified Prelude
import qualified BinNums
import qualified BinPos
import qualified Datatypes
import qualified Decimal
import qualified PosDef

_Z__of_nat :: Datatypes.Coq_nat -> BinNums.Z
_Z__of_nat n =
  case n of {
   Datatypes.O -> BinNums.Z0;
   Datatypes.S n0 -> BinNums.Zpos (PosDef._Pos__of_succ_nat n0)}

_Z__to_int :: BinNums.Z -> Decimal.Coq_signed_int
_Z__to_int n =
  case n of {
   BinNums.Z0 -> Decimal.Pos (Decimal.D0 Decimal.Nil);
   BinNums.Zpos p -> Decimal.Pos (BinPos._Pos__to_uint p);
   BinNums.Zneg p -> Decimal.Neg (BinPos._Pos__to_uint p)}

