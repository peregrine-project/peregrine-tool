{-# LANGUAGE NamedFieldPuns, FlexibleInstances, DeriveAnyClass #-}
{-# LANGUAGE DeriveTraversable #-}
module Agda2Lambox.Compile.Utils
  ( modNameToModPath
  , qnameToKName
  , qnameToName
  , qnameToIdent
  , domToName
  , dataOrRecDefMutuals
  , dataOrRecMutuals
  , toInductive
  , toConApp
  , MayBeLogical(isLogical)
  , sanitize
  ) where

import Control.Monad.State
import Control.Monad.IO.Class ( liftIO )
import Numeric ( showHex )
import Data.Char
import Data.List ( elemIndex, foldl' )
import Data.Maybe ( fromMaybe, listToMaybe, isJust )

import Unicode.Char.Identifiers ( isXIDStart, isXIDContinue )
import Agda.Compiler.Backend
import Agda.Syntax.Internal
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common.Pretty ( prettyShow, Doc )
import Agda.Syntax.Common ( usableModality, Arg(..) )
import Agda.TypeChecking.Datatypes ( getConstructors, getConstructorData )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.Monad.SizedTypes ( isSizeType )
import Agda.TypeChecking.Monad.Base ( TCM )
import Agda.TypeChecking.Substitute (TelV(TelV))
import Agda.TypeChecking.Telescope (telView)
import Agda.Utils.Monad (orM)

import Agda2Lambox.Compile.Monad
import LambdaBox qualified as LBox

-- | Convert and Agda module name to its "equivalent" λ□ module path.
modNameToModPath :: ModuleName -> LBox.ModPath
modNameToModPath =
  LBox.MPFile . map (sanitize . prettyShow) . mnameToList

-- | Convert and Agda definition name to a λ□ kernel name.
qnameToKName :: QName -> LBox.KerName
qnameToKName qn =
  LBox.KerName
    (modNameToModPath $ qnameModule qn)
    (qnameToIdent qn)

domToName :: Dom' a b -> LBox.Name
domToName = maybe LBox.Anon (LBox.Named . sanitize . prettyShow) . domName

qnameToIdent :: QName -> LBox.Ident
qnameToIdent = sanitize . prettyShow . qnameName

qnameToName :: QName -> LBox.Name
qnameToName = LBox.Named . qnameToIdent

dataOrRecDefMutuals :: Definition -> TCM [QName]
dataOrRecDefMutuals d = do
  case theDef d of
    Datatype{dataMutual} -> pure $ fromMaybe [] dataMutual
    Record  {recMutual}  -> pure $ fromMaybe [] recMutual
    _                    -> internalError "Not a datatype or record"

dataOrRecMutuals :: QName -> TCM [QName]
dataOrRecMutuals q = dataOrRecDefMutuals =<< getConstInfo q

-- | Fetch the λ□ inductive associated with a @QName@.
toInductive :: QName -> TCM LBox.Inductive
toInductive q = do
  names <- dataOrRecMutuals q
  let repr = fromMaybe q $ listToMaybe names
  let idx  = fromMaybe 0 $ elemIndex q names
  pure $ LBox.Inductive (qnameToKName repr) idx


-- | Compile a constructor application to λ□.
toConApp :: QName -> [LBox.Term] -> CompileM LBox.Term
toConApp qn es = do
  dt   <- getConstructorData qn
  ctrs <- liftTCM $ getConstructors dt
  ind  <- liftTCM $ toInductive dt
  let idx = fromMaybe 0 $ qn `elemIndex` ctrs

  -- if the blocks option is disabled
  -- no argument is given to LConstruct
  -- and we instead use regular application
  nb <- asks blocks
  if nb then pure $ LBox.LConstruct ind idx es
        else pure $ foldl' LBox.LApp (LBox.LConstruct ind idx []) es



-- | Class for things that may be considered logical, and thus erased.
-- See https://arxiv.org/pdf/2108.02995 for the precise definition.
--
class MayBeLogical a where
  isLogical :: a -> TCM Bool

-- * Logical types
--
-- Note that we may also want to consider logical products
-- into logical types?, Say "proof builders", or "level builders", etc.

-- | Logical types.
--
-- A type is considered logical when it is a proposition
-- (its inhabitants are proofs) or when it is an arity in Prop.
--
-- @Size@ and @Level@ are also considered logical.
instance MayBeLogical Type where
  isLogical typ = orM
    [ pure $ isLogicalSort $ getSort typ
    , isLevelType typ
    , isJust <$> isSizeType typ
    , do TelV tel typ <- telView typ
         case unEl typ of
           Sort s -> pure $ isLogicalSort s
           _      -> pure False
    ]
    where
      isLogicalSort :: Sort -> Bool
      isLogicalSort = \case
        Prop{}      -> True -- Prop
        Inf UProp _ -> True -- Propw
        SizeUniv{}  -> True -- SizeUniv
        LevelUniv{} -> True -- LevelUniv
        _           -> False

-- | Additionally, we consider erased domains logical.
instance MayBeLogical a => MayBeLogical (Dom a) where
  isLogical dom | not (usableModality dom) = pure True
  isLogical dom = isLogical $ unDom dom

instance MayBeLogical a => MayBeLogical (Arg a) where
  isLogical arg | not (usableModality arg) = pure True
  isLogical arg = isLogical $ unArg arg

-- | Delimitor used for name sanitization
sDelim :: Char
sDelim = 'Ֆ'

-- | Sanitize an agda name to a Rust-compatible identifier.
-- Injective by design.
sanitize :: String -> String
sanitize [] = sDelim : "empty" -- NOTE(): should be unreachable
sanitize s@(x:xs)
  -- NOTE(): Rust keywords are converted into raw identifiers
  | s `elem` rustKeywords = "r#"   ++ s
  -- NOTE(): or prefixed with the
  | s `elem` forbiddenRaw = sDelim : s
  | otherwise =
      let hd = escapeChar isXIDStart x
          tl = concatMap (escapeChar isXIDContinue) xs
      in hd <> tl
  where
    escapeChar :: (Char -> Bool) -> Char -> String
    escapeChar xid x = if xid x then [x] else sDelim : esc x
      where
        esc '_'  = "_" -- Preserve underscore (it's gonna get prefixed)
        esc '+'  = "plus"
        esc '-'  = "sub"
        esc '*'  = "mult"
        esc '/'  = "div"
        esc '='  = "eq"
        esc '<'  = "lt"
        esc '>'  = "gt"
        esc 'λ'  = "lam"
        esc '→'  = "to"
        esc '∷'  = "cons"
        esc '?'  = "qen"
        esc '!'  = "bng"
        esc '#'  = "hsh"  -- This ensures names starting with # are escaped
                          -- and enforces injectivity of the sanitization
        esc '.'  = "dot"
        esc c | c == sDelim   = [sDelim]
              | otherwise     = showHex (ord c) [sDelim]

      -- standard rust keywords
    rustKeywords =
      [ "as", "break", "const", "continue", "else", "enum", "extern"
      , "false", "fn", "for", "if", "impl", "in", "let", "loop", "match"
      , "mod", "move", "mut", "pub", "ref", "return", "static", "struct"
      , "trait", "true", "type", "unsafe", "use", "where", "while"
      , "async", "await", "dyn"
      ]

    -- rust keywords that are also forbidden inside raw strings
    forbiddenRaw = ["self", "Self", "super", "crate"]
