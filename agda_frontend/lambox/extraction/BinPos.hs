module BinPos where

import qualified Prelude
import qualified BinNums
import qualified Decimal

_Pos__succ :: BinNums.Coq_positive -> BinNums.Coq_positive
_Pos__succ x =
  case x of {
   BinNums.Coq_xI p -> BinNums.Coq_xO (_Pos__succ p);
   BinNums.Coq_xO p -> BinNums.Coq_xI p;
   BinNums.Coq_xH -> BinNums.Coq_xO BinNums.Coq_xH}

_Pos__add :: BinNums.Coq_positive -> BinNums.Coq_positive ->
             BinNums.Coq_positive
_Pos__add x y =
  case x of {
   BinNums.Coq_xI p ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xO (_Pos__add_carry p q);
     BinNums.Coq_xO q -> BinNums.Coq_xI (_Pos__add p q);
     BinNums.Coq_xH -> BinNums.Coq_xO (_Pos__succ p)};
   BinNums.Coq_xO p ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xI (_Pos__add p q);
     BinNums.Coq_xO q -> BinNums.Coq_xO (_Pos__add p q);
     BinNums.Coq_xH -> BinNums.Coq_xI p};
   BinNums.Coq_xH ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xO (_Pos__succ q);
     BinNums.Coq_xO q -> BinNums.Coq_xI q;
     BinNums.Coq_xH -> BinNums.Coq_xO BinNums.Coq_xH}}

_Pos__add_carry :: BinNums.Coq_positive -> BinNums.Coq_positive ->
                   BinNums.Coq_positive
_Pos__add_carry x y =
  case x of {
   BinNums.Coq_xI p ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xI (_Pos__add_carry p q);
     BinNums.Coq_xO q -> BinNums.Coq_xO (_Pos__add_carry p q);
     BinNums.Coq_xH -> BinNums.Coq_xI (_Pos__succ p)};
   BinNums.Coq_xO p ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xO (_Pos__add_carry p q);
     BinNums.Coq_xO q -> BinNums.Coq_xI (_Pos__add p q);
     BinNums.Coq_xH -> BinNums.Coq_xO (_Pos__succ p)};
   BinNums.Coq_xH ->
    case y of {
     BinNums.Coq_xI q -> BinNums.Coq_xI (_Pos__succ q);
     BinNums.Coq_xO q -> BinNums.Coq_xO (_Pos__succ q);
     BinNums.Coq_xH -> BinNums.Coq_xI BinNums.Coq_xH}}

_Pos__mul :: BinNums.Coq_positive -> BinNums.Coq_positive ->
             BinNums.Coq_positive
_Pos__mul x y =
  case x of {
   BinNums.Coq_xI p -> _Pos__add y (BinNums.Coq_xO (_Pos__mul p y));
   BinNums.Coq_xO p -> BinNums.Coq_xO (_Pos__mul p y);
   BinNums.Coq_xH -> y}

_Pos__to_little_uint :: BinNums.Coq_positive -> Decimal.Coq_uint
_Pos__to_little_uint p =
  case p of {
   BinNums.Coq_xI p0 ->
    Decimal._Little__succ_double (_Pos__to_little_uint p0);
   BinNums.Coq_xO p0 -> Decimal._Little__double (_Pos__to_little_uint p0);
   BinNums.Coq_xH -> Decimal.D1 Decimal.Nil}

_Pos__to_uint :: BinNums.Coq_positive -> Decimal.Coq_uint
_Pos__to_uint p =
  Decimal.rev (_Pos__to_little_uint p)

