-- Boilerplate for Haskell compilation

module Haskell where

{-# FOREIGN GHC {-# LANGUAGE LambdaCase #-} #-}

open import Agda.Builtin.IO         public
open import Agda.Builtin.String
  renaming (primShowNat to showNat) public

open import Prelude

{-# FOREIGN GHC import System.Environment (getArgs) #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import Data.Functor ((<&>)) #-}

postulate
  _>>=_    : IO A → (A → IO B) → IO B
  _>>_     : IO A → IO B → IO B
  return   : A → IO A
  putStrLn : String → IO ⊤
  getInput : Nat → IO Nat
{-# COMPILE GHC _>>=_    = \_ _ _ _ -> (>>=)  #-}
{-# COMPILE GHC _>>_     = \_ _ _ _ -> (>>)  #-}
{-# COMPILE GHC return   = \_ _ -> return #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC getInput = getInput #-}

infixr -1 _$_
_$_ : (A → B) → A → B
f $ x = f x
{-# INLINE _$_ #-}

{-# FOREIGN GHC

  -- | Try to read an integer from std input args
  -- otherwise use default value
  getInput :: Integer -> IO Integer
  getInput n = getArgs <&> \case
    [s] -> read s
    _   -> n

#-}
