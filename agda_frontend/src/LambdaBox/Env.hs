{-# LANGUAGE DataKinds, GADTs, OverloadedStrings #-}
{- |
Module      : LambdaBox.Env
Description : Lambda Box environments, identical for both targets.

In this module, we define all the building blocks that make up
a λ□ global environment.

Because we want to target both the untyped and typed-annotated variants
of λ□, but would rather use a single unified global environment,
we parametrize most definitions with a typing mode 'Agda2Lambox.Compile.Target.Typing'.

This ensures that the typing information /is always there/ when targetting the
typed target, while also avoiding to do unnecessary work when type information is not required.
-}
module LambdaBox.Env where



import Data.Kind ( Type )
import Data.List.NonEmpty ( NonEmpty )

import Agda.Syntax.Common.Pretty

import LambdaBox.Names
import LambdaBox.Term
import LambdaBox.Type qualified as LBox
import LambdaBox.Target
import LambdaBox.LambdaBox




-- pretty-printing
----------------------------

instance Pretty (ConstructorBody t) where
  pretty Constructor{..} =
    vcat
    [ pretty cstrName <+> parens (pretty cstrArgs <+> "arg(s)")
    , nest 2 $ flip foldMap cstrTypes \args ->
        vcat $ flip map args \(name, typ) ->
          pretty name  <+> ":" <+> pretty typ
    ]

instance Pretty TypeVarInfo where
  pretty TypeVarInfo{..} = pretty tvarName

instance Pretty (OneInductiveBody t) where
  pretty OneInductive{..} = vcat
    [ pretty indName
    , flip foldMap indTypeVars \tvs -> "type variables: " <+> pretty tvs
    , nest 2 $ hang "constructors:" 2 $ vcat $ map pretty indCtors
    ]

instance Pretty (GlobalDecl t) where
  pretty = \case
    ConstantDecl ConstantBody{..} ->
      hang "constant declaration:" 2 $ vcat
        [ flip foldMap cstType \(tvs, typ) ->
            vcat [ "type variables:" <+> pretty tvs
                 ,  "type:" <+> pretty typ
                  ]
        , "body:" <+> pretty cstBody
        ]

    InductiveDecl MutualInductive{..} ->
      hang "mutual inductive(s):" 2 $
        vsep $ map pretty indBodies

    TypeAliasDecl decl ->
      hang "type alias:" 2 $ case decl of
        Nothing -> mempty
        Just (vars, typ) -> vcat
          [ "type variables:" <+> pretty vars
          , "type:" <+> pretty typ
          ]

instance Pretty (GlobalEnv t) where
  pretty (GlobalEnv env) =
    vsep $ flip map (reverse env) \(kn, d) ->
      hang (pretty kn <> ":") 2 (pretty d)

instance Pretty (LBoxModule t) where
  pretty LBoxModule{..} = vcat
    [ pretty lboxEnv
    , flip foldMap lboxMain \kn -> "main program:" <+> pretty kn
    ]
