{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      : LambdaBox
-- Description : Lambda Box ASTs, identical for both targets.
--
-- In this module, we define all the building blocks that make up
-- a λ□ global environment and λ□ terms.
--
-- Because we want to target both the untyped and typed-annotated variants
-- of λ□, but would rather use a single unified global environment,
-- we parametrize most definitions with a typing mode 'Agda2Lambox.Compile.Target.Typing'.
--
-- This ensures that the typing information /is always there/ when targetting the
-- typed target, while also avoiding to do unnecessary work when type information is not required.

-- Lambda Box AST definition
module LambdaBox.LambdaBox where

import Data.Int (Int64)
import qualified Data.Kind
import Data.List.NonEmpty ( NonEmpty )

import LambdaBox.Target



-- Identifiers
type Ident = String

-- Directory path
type DirPath = [Ident]

-- Module path
data ModPath
  = MPFile DirPath
  | MPBound DirPath Ident Int
  | MPDot ModPath Ident

-- Rocq kernel names donoting object identifier and path
data KerName = KerName
  { kerModPath :: ModPath,
    kerName :: Ident
  }

-- Identifier of an inductive
data Inductive = Inductive
  { -- Kername of the mututal inductives block
    indMInd :: KerName,
    -- index of the inductive in the mutual inductives block
    indInd :: Int
  }

-- Record projection
data Projection = ProjectionIdent
   { --
    projInd :: Inductive,
    -- Number of (non-let parameters)
    projNPars :: Int,
    -- Argument to project
    projArg :: Int
  }

-- Names used in binders
data Name
  = Anon
  | Named Ident



-- Lambda Box Types
data Type
  = TBox
  | TAny
  | TArr Type Type
  | TApp Type Type
  | TVar Int
  | TInd Inductive
  | TConst KerName

-- Type variable information.
--
-- See [Extracting functional programs from Coq, in Coq](https://arxiv.org/pdf/2108.02995)
-- for the full explanation.
--
-- * A type is an /arity/ if it is a (possibly nullary) product into a sort.
--
--    So of the shape @∀ (a₁ : A₁) ... (a_n : A_n) → s@ with @s@ being @Type@ or @Prop@.
--
--    Inhabitants of arities are called /type schemes/.
--
-- * A type is /logical/ when it is a proposition (i.e. inhabitants are proofs)
--  or when it is an /arity/ into @Prop@.
--
--    * @P@ when @P : Prop@.
--    * @∀ (a₁ : A₁) ... (a_n : A_n) → Prop@ (i.e. inhabitants are propositional type schemes).
--
-- * A type is a sort when it is either @Prop@ or @Type@.
--
--    Note that a sort is always a /nullary/ arity.
--
-- A few examples:
--
-- * @Type@ is an arity and a sort, but not logical.
-- * @P@ with @P : Prop@ is logical, but neither an arity nor a sort.
-- * @Type → Prop@ is logical, an arity, but not a sort.
-- * @Type → Type@ is an arity, but neither a sort nor logical.
-- * @∀ (A : Type) → A → A@ is neither of the three.
data TypeVarInfo = TypeVarInfo
  { tvarName :: Name,
    tvarIsArity :: Bool,
    tvarIsLogical :: Bool,
    tvarIsSort :: Bool
  }



-- Definitions of mutual fixpoints
data Def t = Def
  { -- Fixpoint name
    dName :: Name,
    -- Fixpoint body
    dBody :: t,
    -- Number of arguments
    dArgs :: Int
  }

type MFixpoint = [Def Term]

-- Primitives
data PrimValue a
  = PInt Int64
  | PFloat Double
  | PString String
  | PArray a [a]

-- Lambda Box terms
data Term
  = -- Proofs and erased terms
    LBox
  | -- Bound variable, with de Bruijn index
    LRel Int
  | -- Free variable
    LVar Ident
  | -- EVars
    LEvar Int [Term]
  | -- Lambda abstraction
    LLambda Name Term
  | -- Let bindings
    LLetIn Name Term Term
  | -- Term application
    LApp Term Term
  | -- Named constant
    LConst KerName
  | -- Inductive constructor
    LConstruct Inductive Int [Term]
  | -- Pattern-matching case construct
    LCase
      -- Inductive type we case on
      Inductive
      -- Number of parameters
      Int
      -- Discriminee
      Term
      -- Branches
      [([Name], Term)]
  | -- Projection
    LProj Projection Term
  | -- Fixpoint combinator
    LFix
      MFixpoint
      -- Index of the fixpoint we keep
      Int
  | -- CoFixpoint combinator
    LCoFix
      MFixpoint
      -- Index of the fixpoint we keep
      Int
  | -- Primitive literal value
    LPrim (PrimValue Term)
  | -- Lazy evaluation
    LLazy Term
  | -- Force evaluation
    LForce Term



-- Allowed elimination target for a datatype
data AllowedElims
  = IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny

data RecursivityKind
  = -- Inductive datatype
    Finite
  | -- Coinductive datatype
    CoFinite
  | -- Non-recursive (records, variants)
    BiFinite

-- Constructor info in an inductive datatype.
data ConstructorBody t = Constructor
  { cstrName :: Ident,
    cstrArgs :: Int,
    cstrTypes :: WhenTyped t [(Name, Type)]
  }

-- Projection info in an inductive datatype.
data ProjectionBody t = Projection
  { projName :: Ident,
    projType :: WhenTyped t Type
  }

-- Inductive datatype declaration body
data OneInductiveBody t = OneInductive
  { indName :: Ident,
    indPropositional :: Bool,
    indKElim :: AllowedElims,
    indTypeVars :: WhenTyped t [TypeVarInfo],
    indCtors :: [ConstructorBody t],
    indProjs :: [ProjectionBody t]
  }

-- Declaration of mutually defined inductive types
data MutualInductiveBody t = MutualInductive
  { indFinite :: RecursivityKind,
    indPars :: Int,
    indBodies :: [OneInductiveBody t]
  }

-- Definition of a constant in the environment
data ConstantBody t = ConstantBody
  { cstType :: WhenTyped t ([Name], Type),
    cstBody :: Maybe Term
  }

-- Global declarations.
data GlobalDecl (t :: Typing) :: Data.Kind.Type where
  ConstantDecl :: ConstantBody t -> GlobalDecl t
  InductiveDecl :: MutualInductiveBody t -> GlobalDecl t
  TypeAliasDecl :: Maybe ([TypeVarInfo], Type) -> GlobalDecl Typed

-- Global environment.
newtype GlobalEnv t = GlobalEnv [(KerName, GlobalDecl t)]

-- Generated module
data LBoxModule t = LBoxModule
  { lboxEnv :: GlobalEnv t,
    lboxMain :: WhenUntyped t (NonEmpty KerName)
  }
