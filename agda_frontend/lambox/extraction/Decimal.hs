module Decimal where

import qualified Prelude

data Coq_uint =
   Nil
 | D0 Coq_uint
 | D1 Coq_uint
 | D2 Coq_uint
 | D3 Coq_uint
 | D4 Coq_uint
 | D5 Coq_uint
 | D6 Coq_uint
 | D7 Coq_uint
 | D8 Coq_uint
 | D9 Coq_uint

data Coq_signed_int =
   Pos Coq_uint
 | Neg Coq_uint

revapp :: Coq_uint -> Coq_uint -> Coq_uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Coq_uint -> Coq_uint
rev d =
  revapp d Nil

_Little__double :: Coq_uint -> Coq_uint
_Little__double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (_Little__double d0);
   D1 d0 -> D2 (_Little__double d0);
   D2 d0 -> D4 (_Little__double d0);
   D3 d0 -> D6 (_Little__double d0);
   D4 d0 -> D8 (_Little__double d0);
   D5 d0 -> D0 (_Little__succ_double d0);
   D6 d0 -> D2 (_Little__succ_double d0);
   D7 d0 -> D4 (_Little__succ_double d0);
   D8 d0 -> D6 (_Little__succ_double d0);
   D9 d0 -> D8 (_Little__succ_double d0)}

_Little__succ_double :: Coq_uint -> Coq_uint
_Little__succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (_Little__double d0);
   D1 d0 -> D3 (_Little__double d0);
   D2 d0 -> D5 (_Little__double d0);
   D3 d0 -> D7 (_Little__double d0);
   D4 d0 -> D9 (_Little__double d0);
   D5 d0 -> D1 (_Little__succ_double d0);
   D6 d0 -> D3 (_Little__succ_double d0);
   D7 d0 -> D5 (_Little__succ_double d0);
   D8 d0 -> D7 (_Little__succ_double d0);
   D9 d0 -> D9 (_Little__succ_double d0)}

