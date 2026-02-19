module BinNat where

import qualified Prelude
import qualified BinNums
import qualified BinPos
import qualified Datatypes
import qualified PosDef

_N__compare :: BinNums.N -> BinNums.N -> Datatypes.Coq_comparison
_N__compare n m =
  case n of {
   BinNums.N0 ->
    case m of {
     BinNums.N0 -> Datatypes.Eq;
     BinNums.Npos _ -> Datatypes.Lt};
   BinNums.Npos n' ->
    case m of {
     BinNums.N0 -> Datatypes.Gt;
     BinNums.Npos m' -> PosDef._Pos__compare n' m'}}

_N__add :: BinNums.N -> BinNums.N -> BinNums.N
_N__add n m =
  case n of {
   BinNums.N0 -> m;
   BinNums.Npos p ->
    case m of {
     BinNums.N0 -> n;
     BinNums.Npos q -> BinNums.Npos (BinPos._Pos__add p q)}}

_N__mul :: BinNums.N -> BinNums.N -> BinNums.N
_N__mul n m =
  case n of {
   BinNums.N0 -> BinNums.N0;
   BinNums.Npos p ->
    case m of {
     BinNums.N0 -> BinNums.N0;
     BinNums.Npos q -> BinNums.Npos (BinPos._Pos__mul p q)}}

_N__eqb :: BinNums.N -> BinNums.N -> Prelude.Bool
_N__eqb n m =
  case n of {
   BinNums.N0 ->
    case m of {
     BinNums.N0 -> Prelude.True;
     BinNums.Npos _ -> Prelude.False};
   BinNums.Npos p ->
    case m of {
     BinNums.N0 -> Prelude.False;
     BinNums.Npos q -> PosDef._Pos__eqb p q}}

_N__to_nat :: BinNums.N -> Datatypes.Coq_nat
_N__to_nat a =
  case a of {
   BinNums.N0 -> Datatypes.O;
   BinNums.Npos p -> PosDef._Pos__to_nat p}

_N__of_nat :: Datatypes.Coq_nat -> BinNums.N
_N__of_nat n =
  case n of {
   Datatypes.O -> BinNums.N0;
   Datatypes.S n' -> BinNums.Npos (PosDef._Pos__of_succ_nat n')}

