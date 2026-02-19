{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Datatypes where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

data Coq_nat =
   O
 | S Coq_nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

data Coq_comparison =
   Eq
 | Lt
 | Gt

id :: Any -> Any
id x =
  x

