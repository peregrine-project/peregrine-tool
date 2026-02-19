module PeanoNat where

import qualified Prelude
import qualified Datatypes

_Nat__sub :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__sub n m =
  case n of {
   Datatypes.O -> n;
   Datatypes.S k ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S l -> _Nat__sub k l}}

_Nat__divmod :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
                -> Datatypes.Coq_nat -> (,) Datatypes.Coq_nat
                Datatypes.Coq_nat
_Nat__divmod x y q u =
  case x of {
   Datatypes.O -> (,) q u;
   Datatypes.S x' ->
    case u of {
     Datatypes.O -> _Nat__divmod x' y (Datatypes.S q) y;
     Datatypes.S u' -> _Nat__divmod x' y q u'}}

_Nat__div :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__div x y =
  case y of {
   Datatypes.O -> y;
   Datatypes.S y' -> Datatypes.fst (_Nat__divmod x y' Datatypes.O y')}

_Nat__modulo :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__modulo x y =
  case y of {
   Datatypes.O -> x;
   Datatypes.S y' ->
    _Nat__sub y' (Datatypes.snd (_Nat__divmod x y' Datatypes.O y'))}

