{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

-- | Compile targets for the backend
module LambdaBox.Target
  ( Typing (..),
    Target (..),
    WhenTyped (..),
    WhenUntyped (..),
    getTyped,
    getUntyped,
    whenTyped,
    whenUntyped,
  )
where

import Control.DeepSeq (NFData (rnf))
import Data.Foldable (Foldable (foldMap))
import Data.Kind (Type)

-- | Supported targets.
data Typing = Typed | Untyped

-- | Compile targets, indexed by the typing mode.
data Target :: Typing -> Type where
  ToTyped :: Target Typed
  ToUntyped :: Target Untyped

-- | Type wrapper that contains a value iff we're in the typed setting.
data WhenTyped (t :: Typing) (a :: Type) :: Type where
  None :: WhenTyped Untyped a
  Some :: a -> WhenTyped Typed a

data ATyped (t :: Typing) (a :: Type) (b :: Type) :: Type where
  SomeTT :: a -> ATyped Untyped a b
  SomeUU :: b -> ATyped Typed a b

instance Functor (WhenTyped t) where
  fmap f None = None
  fmap f (Some x) = Some (f x)

instance Applicative (WhenTyped Typed) where
  pure = Some
  Some f <*> Some x = Some (f x)

instance Monad (WhenTyped Typed) where
  Some x >>= f = f x

instance Foldable (WhenTyped t) where
  foldMap f None = mempty
  foldMap f (Some x) = f x

-- | Type wrapper that contains a value iff we're in the untyped setting.
data WhenUntyped (t :: Typing) (a :: Type) :: Type where
  NoneU :: WhenUntyped Typed a
  SomeU :: a -> WhenUntyped Untyped a

instance Functor (WhenUntyped t) where
  fmap f NoneU = NoneU
  fmap f (SomeU x) = SomeU (f x)

instance Applicative (WhenUntyped Untyped) where
  pure = SomeU
  SomeU f <*> SomeU x = SomeU (f x)

instance Monad (WhenUntyped Untyped) where
  SomeU x >>= f = f x

instance Foldable (WhenUntyped t) where
  foldMap f NoneU = mempty
  foldMap f (SomeU x) = f x

-- | Retrieve a value when it's there for sure, in the typed setting.
getTyped :: WhenTyped Typed a -> a
getTyped (Some x) = x

-- | Retrieve a value when it's there for sure, in the untyped setting.
getUntyped :: WhenUntyped Untyped a -> a
getUntyped (SomeU x) = x

-- | Only perform a computation when targetting typed.
whenTyped :: (Applicative m) => Target t -> m a -> m (WhenTyped t a)
whenTyped ToUntyped _ = pure None
whenTyped ToTyped x = Some <$> x

-- | Only perform a computation when targetting untyped.
whenUntyped :: (Applicative m) => Target t -> m a -> m (WhenUntyped t a)
whenUntyped ToTyped _ = pure NoneU
whenUntyped ToUntyped x = SomeU <$> x

instance NFData (Target t) where
  rnf ToTyped = ()
  rnf ToUntyped = ()
