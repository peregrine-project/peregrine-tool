module PosDef where

import qualified Prelude
import qualified BinNums
import qualified Datatypes
import qualified Nat0

_Pos__succ :: BinNums.Coq_positive -> BinNums.Coq_positive
_Pos__succ x =
  case x of {
   BinNums.Coq_xI p -> BinNums.Coq_xO (_Pos__succ p);
   BinNums.Coq_xO p -> BinNums.Coq_xI p;
   BinNums.Coq_xH -> BinNums.Coq_xO BinNums.Coq_xH}

_Pos__compare_cont :: Datatypes.Coq_comparison -> BinNums.Coq_positive ->
                      BinNums.Coq_positive -> Datatypes.Coq_comparison
_Pos__compare_cont r x y =
  case x of {
   BinNums.Coq_xI p ->
    case y of {
     BinNums.Coq_xI q -> _Pos__compare_cont r p q;
     BinNums.Coq_xO q -> _Pos__compare_cont Datatypes.Gt p q;
     BinNums.Coq_xH -> Datatypes.Gt};
   BinNums.Coq_xO p ->
    case y of {
     BinNums.Coq_xI q -> _Pos__compare_cont Datatypes.Lt p q;
     BinNums.Coq_xO q -> _Pos__compare_cont r p q;
     BinNums.Coq_xH -> Datatypes.Gt};
   BinNums.Coq_xH -> case y of {
                      BinNums.Coq_xH -> r;
                      _ -> Datatypes.Lt}}

_Pos__compare :: BinNums.Coq_positive -> BinNums.Coq_positive ->
                 Datatypes.Coq_comparison
_Pos__compare =
  _Pos__compare_cont Datatypes.Eq

_Pos__eqb :: BinNums.Coq_positive -> BinNums.Coq_positive -> Prelude.Bool
_Pos__eqb p q =
  case p of {
   BinNums.Coq_xI p0 ->
    case q of {
     BinNums.Coq_xI q0 -> _Pos__eqb p0 q0;
     _ -> Prelude.False};
   BinNums.Coq_xO p0 ->
    case q of {
     BinNums.Coq_xO q0 -> _Pos__eqb p0 q0;
     _ -> Prelude.False};
   BinNums.Coq_xH ->
    case q of {
     BinNums.Coq_xH -> Prelude.True;
     _ -> Prelude.False}}

_Pos__iter_op :: (a1 -> a1 -> a1) -> BinNums.Coq_positive -> a1 -> a1
_Pos__iter_op op p a =
  case p of {
   BinNums.Coq_xI p0 -> op a (_Pos__iter_op op p0 (op a a));
   BinNums.Coq_xO p0 -> _Pos__iter_op op p0 (op a a);
   BinNums.Coq_xH -> a}

_Pos__to_nat :: BinNums.Coq_positive -> Datatypes.Coq_nat
_Pos__to_nat x =
  _Pos__iter_op Nat0.add x (Datatypes.S Datatypes.O)

_Pos__of_succ_nat :: Datatypes.Coq_nat -> BinNums.Coq_positive
_Pos__of_succ_nat n =
  case n of {
   Datatypes.O -> BinNums.Coq_xH;
   Datatypes.S x -> _Pos__succ (_Pos__of_succ_nat x)}

