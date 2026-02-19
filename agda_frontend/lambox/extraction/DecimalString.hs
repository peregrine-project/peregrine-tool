module DecimalString where

import qualified Prelude
import qualified Decimal
import Data.Char (ord)
import Data.Bits (testBit)

_NilEmpty__string_of_uint :: Decimal.Coq_uint -> Prelude.String
_NilEmpty__string_of_uint d =
  case d of {
   Decimal.Nil -> "";
   Decimal.D0 d0 -> (:) '0' (_NilEmpty__string_of_uint d0);
   Decimal.D1 d0 -> (:) '1' (_NilEmpty__string_of_uint d0);
   Decimal.D2 d0 -> (:) '2' (_NilEmpty__string_of_uint d0);
   Decimal.D3 d0 -> (:) '3' (_NilEmpty__string_of_uint d0);
   Decimal.D4 d0 -> (:) '4' (_NilEmpty__string_of_uint d0);
   Decimal.D5 d0 -> (:) '5' (_NilEmpty__string_of_uint d0);
   Decimal.D6 d0 -> (:) '6' (_NilEmpty__string_of_uint d0);
   Decimal.D7 d0 -> (:) '7' (_NilEmpty__string_of_uint d0);
   Decimal.D8 d0 -> (:) '8' (_NilEmpty__string_of_uint d0);
   Decimal.D9 d0 -> (:) '9' (_NilEmpty__string_of_uint d0)}

_NilEmpty__string_of_int :: Decimal.Coq_signed_int -> Prelude.String
_NilEmpty__string_of_int d =
  case d of {
   Decimal.Pos d0 -> _NilEmpty__string_of_uint d0;
   Decimal.Neg d0 -> (:) '-' (_NilEmpty__string_of_uint d0)}

