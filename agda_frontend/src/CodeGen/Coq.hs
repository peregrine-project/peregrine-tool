{-# LANGUAGE FlexibleInstances, FlexibleContexts, OverloadedStrings, DataKinds, MonadComprehensions #-}
-- | Generating Coq code from our LambdaBox AST
module CodeGen.Coq (prettyCoq) where

import Data.Bifunctor(bimap)
import Data.List(intercalate)
import Data.List.NonEmpty qualified as NEL

import Agda.Syntax.Common.Pretty
import LambdaBox
import Agda.Utils.Function (applyWhen)
import LambdaBox.Target


class ToCoq t a where
  pcoq  :: Target t -> a -> Doc
  pcoqP :: Int -> Target t -> a -> Doc
  pcoq  = pcoqP 0
  pcoqP = const pcoq
  {-# MINIMAL pcoq | pcoqP #-}

-- | Shorthand for untyped λ□ pretty-printer.
upcoq :: ToCoq Untyped a => a -> Doc
upcoq = pcoq ToUntyped

-- | Shorthand for typed λ□ pretty-printer.
tpcoq :: ToCoq Typed a => a -> Doc
tpcoq = pcoq ToTyped

-- | Pretty-print a Coq-printable term.
prettyCoq :: ToCoq t a => Target t -> a -> String
prettyCoq t = render . pcoq t

-- | Util to format Coq constructor with the given arguments.
ctor :: String -> [Doc] -> Doc
ctor = ctorP 0
{-# INLINE ctor #-}

-- | Util to format Coq constructor with the given arguments (and precedence).
ctorP :: Int -> String -> [Doc] -> Doc
ctorP p name []   = text name
ctorP p name args = applyWhen (p >= 10) parens $ text name <?> fsep args

-- | Util to format Coq record value with the given fields.
record :: [(String, Doc)] -> Doc
record = enclose
       . fsep
       . punctuate semi
       . map \(k, v) -> hang (text k <+> ":=") 2 v
  where enclose x = "{|" <+> x <+> "|}"

instance ToCoq t Doc  where pcoq _ d = d
instance ToCoq t Int  where pcoq _ s = pretty s
instance ToCoq t Bool where pcoq _ v = if v then "true" else "false"

quote :: String -> String
quote s = "\"" <> escape s <> "\""
  where
    escape []       = []
    escape ('"':cs) = "\\\"" <> escape cs
    escape (c  :cs) = c : escape cs

instance {-# OVERLAPPING #-} ToCoq t String where
  pcoq _ s = text (quote s) <> "%bs"
  -- NOTE(): "%bs" to make sure that we produce Coq bytestrings

instance ToCoq t a => ToCoq t (Maybe a) where
  pcoqP p t x = case x of
    Nothing -> ctorP p "None" []
    Just y  -> ctorP p "Some" [pcoqP 10 t y]

instance ToCoq t a => ToCoq t [a] where
  pcoq t xs = brackets $ fsep $ punctuate ";" $ map (pcoq t) xs

instance (ToCoq t a, ToCoq t b) => ToCoq t (a, b) where
  pcoq t (a, b) = parens $ fsep [pcoq t a <> comma, pcoq t b]

instance ToCoq t Name where
  pcoq t n = case n of
    Anon    -> ctor "nAnon"  []
    Named i -> ctor "nNamed" [pcoq t i]

instance ToCoq t ModPath where
  pcoqP p t mp = case mp of
    MPFile dp       -> ctorP p "MPfile"  [pcoqP 10 t dp]
    MPBound dp id i -> ctorP p "MPbound" [pcoqP 10 t dp, pcoqP 10 t id, pcoqP 10 t i]
    MPDot mp id     -> ctorP p "MPdot"   [pcoqP 10 t mp, pcoqP 10 t id]

instance ToCoq t KerName where
  pcoq t KerName{..} = pcoq t (kerModPath, kerName)

instance ToCoq t Inductive where
  pcoq t Inductive{..} =
    record [ ("inductive_mind", pcoq t indMInd)
           , ("inductive_ind",  pcoq t indInd)
           ]

instance ToCoq t d => ToCoq t (Def d) where
  pcoq t Def{..} =
    record [ ("dname", pcoq t dName)
           , ("dbody", pcoq t dBody)
           , ("rarg",  pcoq t dArgs)
           ]

instance ToCoq t Term where
  pcoqP p t v = case v of
    LBox                -> ctorP p "tBox"       []
    LRel k              -> ctorP p "tRel"       [pretty k]
    LLambda n u         -> ctorP p "tLambda"    [pcoq t n, pcoqP 10 t u]
    LLetIn n u v        -> ctorP p "tLetIn"     [pcoq t n, pcoqP 10 t u, pcoqP 10 t v]
    LApp u v            -> ctorP p "tApp"       [pcoqP 10 t u, pcoqP 10 t v]
    LConst c            -> ctorP p "tConst"     [pcoqP 10 t c]
    LConstruct ind i es -> ctorP p "tConstruct" [pcoqP 10 t ind, pcoqP 10 t i, pcoqP 10 t es]
    LCase ind n u bs    -> ctorP p "tCase"      [pcoqP 10 t (ind, n), pcoqP 10 t u, pcoqP 10 t bs]
    LFix mf i           -> ctorP p "tFix"       [pcoqP 10 t mf, pcoqP 10 t i]

instance ToCoq t Type where
  pcoqP p t v = case v of
    TBox      -> ctorP p "TBox"   []
    TAny      -> ctorP p "TAny"   []
    TArr a b  -> ctorP p "TArr"   [pcoqP 10 t a, pcoqP 10 t b]
    TApp a b  -> ctorP p "TApp"   [pcoqP 10 t a, pcoqP 10 t b]
    TVar k    -> ctorP p "TVar"   [pretty k]
    TInd ind  -> ctorP p "TInd"   [pcoqP 10 t ind]
    TConst kn -> ctorP p "TConst" [pcoqP 10 t kn]

instance ToCoq t RecursivityKind where
  pcoq _ rk = case rk of
    Finite   -> ctor "Finite"   []
    CoFinite -> ctor "CoFinite" []
    BiFinite -> ctor "BiFinite" []

instance ToCoq t AllowedElims where
  pcoq t ae = case ae of
    IntoSProp        -> ctor "IntoSProp"        []
    IntoPropSProp    -> ctor "IntoPropSProp"    []
    IntoSetPropSProp -> ctor "IntoSetPropSProp" []
    IntoAny          -> ctor "IntoAny"          []

instance ToCoq t (ConstructorBody t) where
  pcoq ToUntyped Constructor{..} =
    record [ ("cstr_name",  upcoq cstrName)
           , ("cstr_nargs", upcoq cstrArgs)
           ]

  pcoq ToTyped Constructor{..} =
    tpcoq ((cstrName, getTyped cstrTypes), cstrArgs)

instance ToCoq t (ProjectionBody t) where
  pcoq ToUntyped Projection{..} = record [("proj_name",  upcoq projName)]
  pcoq ToTyped   Projection{..} = tpcoq (projName, getTyped projType)

instance ToCoq t TypeVarInfo where
  pcoq t TypeVarInfo{..} =
    record
      [ ("tvar_name",       pcoq t tvarName)
      , ("tvar_is_logical", pcoq t tvarIsLogical)
      , ("tvar_is_arity",   pcoq t tvarIsArity)
      , ("tvar_is_sort",    pcoq t tvarIsSort)
      ]

instance ToCoq t (OneInductiveBody t) where
  pcoq t OneInductive{..} =
    record $
      [ ("ind_name",          pcoq t indName)
      , ("ind_propositional", pcoq t indPropositional)
      , ("ind_kelim",         pcoq t indKElim)
      , ("ind_ctors",         pcoq t indCtors)
      , ("ind_projs",         pcoq t indProjs)
      ] ++
      case t of
        ToUntyped -> []
        ToTyped   -> [("ind_type_vars", pcoq t $ getTyped indTypeVars)]

instance ToCoq t (MutualInductiveBody t) where
  pcoq t MutualInductive{..} =
    record [ ("ind_finite", pcoq t indFinite)
           , ("ind_npars",  pcoq t indPars)
           , ("ind_bodies", pcoq t indBodies)
           ]

instance ToCoq t (ConstantBody t) where
  pcoqP p t ConstantBody{..} =
    record $
      [("cst_body", pcoq t cstBody)] ++
      case t of
        ToUntyped -> []
        ToTyped   -> [("cst_type", pcoq t $ getTyped cstType)]

instance ToCoq t (GlobalDecl t) where
  pcoqP p t decl = case decl of
    ConstantDecl  body  -> ctorP p "ConstantDecl"  [pcoqP 10 t body]
    InductiveDecl minds -> ctorP p "InductiveDecl" [pcoqP 10 t minds]
    TypeAliasDecl typ   -> ctorP p "TypeAliasDecl" [pcoqP 10 t typ]

instance ToCoq t (GlobalEnv t) where
  pcoq ToUntyped (GlobalEnv env) = upcoq env
  pcoq ToTyped   (GlobalEnv env) = tpcoq $ flip map env \(kn, decl) -> ((kn, True), decl)

instance ToCoq t (LBoxModule t) where
  pcoq ToUntyped LBoxModule{..} = vsep
    [ vcat
        [ "From Coq             Require Import List."
        , "From MetaCoq.Common  Require Import BasicAst Kernames Universes."
        , "From MetaCoq.Utils   Require Import bytestring."
        , "From MetaCoq.Erasure Require Import EAst."
        , "From Agda2Lambox     Require Import CheckWF Eval."
        , "Import ListNotations."
        ]

    , hang "Definition env : global_declarations :=" 2 $
        upcoq lboxEnv <> "."

    , "Compute @check_wf_glob eflags env."

    , vsep $ flip map (zip [1..] $ reverse $ NEL.toList $ getUntyped lboxMain) \(i :: Int, kn) ->
        let progname = "prog" <> pretty i in vsep
        [ hang ("Definition " <> progname <> " : program :=") 2 $
            upcoq (text "env" :: Doc, LConst kn)
            <> "."
        , "Compute eval_program " <> progname <> "."
        ]
    ]

  pcoq ToTyped LBoxModule{..} = vsep
    [ vcat
        [ "From Coq             Require Import List."
        , "From MetaCoq.Common  Require Import BasicAst Kernames Universes."
        , "From MetaCoq.Utils   Require Import bytestring."
        , "From MetaCoq.Erasure Require Import EAst ExAst."
        , "From Agda2Lambox     Require Import CheckWF Eval."
        , "Import ListNotations."
        ]

    , hang "Definition env : global_env :=" 2 $ tpcoq lboxEnv <> "."
    ]
