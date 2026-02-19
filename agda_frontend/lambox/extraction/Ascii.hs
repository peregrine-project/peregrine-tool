module Ascii where

import qualified Prelude
import qualified BinNat
import qualified BinNums
import qualified Datatypes
import Data.Char (ord, chr)
import Data.Bits (testBit, shiftL)

zero :: Prelude.Char
zero =
  '\000'

one :: Prelude.Char
one =
  '\001'

shift :: Prelude.Bool -> Prelude.Char -> Prelude.Char
shift c a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a1 a2 a3 a4 a5 a6 a7 _ ->
    (\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (
      (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+
      (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+
      (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+
      (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+
      (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+
      (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+
      (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+
      (if b7 then Data.Bits.shiftL 1 7 else 0)))
    c a1 a2 a3 a4 a5 a6 a7)
    a

ascii_of_pos :: BinNums.Coq_positive -> Prelude.Char
ascii_of_pos =
  let {
   loop n p =
     case n of {
      Datatypes.O -> zero;
      Datatypes.S n' ->
       case p of {
        BinNums.Coq_xI p' -> shift Prelude.True (loop n' p');
        BinNums.Coq_xO p' -> shift Prelude.False (loop n' p');
        BinNums.Coq_xH -> one}}}
  in loop (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
       (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O))))))))

ascii_of_N :: BinNums.N -> Prelude.Char
ascii_of_N n =
  case n of {
   BinNums.N0 -> zero;
   BinNums.Npos p -> ascii_of_pos p}

ascii_of_nat :: Datatypes.Coq_nat -> Prelude.Char
ascii_of_nat a =
  ascii_of_N (BinNat._N__of_nat a)

coq_N_of_digits :: (([]) Prelude.Bool) -> BinNums.N
coq_N_of_digits l =
  case l of {
   ([]) -> BinNums.N0;
   (:) b l' ->
    BinNat._N__add
      (case b of {
        Prelude.True -> BinNums.Npos BinNums.Coq_xH;
        Prelude.False -> BinNums.N0})
      (BinNat._N__mul (BinNums.Npos (BinNums.Coq_xO BinNums.Coq_xH))
        (coq_N_of_digits l'))}

coq_N_of_ascii :: Prelude.Char -> BinNums.N
coq_N_of_ascii a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a0 a1 a2 a3 a4 a5 a6 a7 ->
    coq_N_of_digits ((:) a0 ((:) a1 ((:) a2 ((:) a3 ((:) a4 ((:) a5 ((:) a6
      ((:) a7 ([]))))))))))
    a

nat_of_ascii :: Prelude.Char -> Datatypes.Coq_nat
nat_of_ascii a =
  BinNat._N__to_nat (coq_N_of_ascii a)

