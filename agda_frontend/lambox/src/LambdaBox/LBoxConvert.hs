-- Conversion to internal representation
module LambdaBox.LBoxConvert where

import qualified Kernames
import qualified Datatypes
import qualified BasicAst
import qualified ExAst
import qualified EAst
import qualified PAst
import qualified Primitive
import qualified EPrimitive
import qualified PrimInt63
import qualified Specif
import qualified Universes0
import qualified Bytestring

import Data.Int (Int64)
import Data.List.NonEmpty qualified as NEL
import LambdaBox.LambdaBox
import LambdaBox.Target (Target (ToTyped, ToUntyped), getTyped, getUntyped)
import Data.Text (pack)
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Char8 (unpack)

stringConv :: String -> Bytestring.String__Coq_t
stringConv s =
  Bytestring._String__of_string $ unpack $ encodeUtf8 $ pack s

natConv :: Int -> Datatypes.Coq_nat
natConv 0 = Datatypes.O
natConv i = Datatypes.S $ natConv $ (i-1)

identConv :: Ident -> Kernames.Coq_ident
identConv i =
  stringConv i

dirPathConv :: DirPath -> Kernames.Coq_dirpath
dirPathConv dp =
  map identConv dp

modPathConv :: ModPath -> Kernames.Coq_modpath
modPathConv (MPFile dp) = Kernames.MPfile $ dirPathConv $ dp
modPathConv (MPBound dp id' i) = Kernames.MPbound (dirPathConv dp) (identConv id') (natConv i)
modPathConv (MPDot mp id') = Kernames.MPdot (modPathConv mp) (identConv id')

kerNameConv :: KerName -> Kernames.Coq_kername
kerNameConv KerName {..} = (modPathConv kerModPath, identConv kerName)

inductiveConv :: Inductive -> Kernames.Coq_inductive
inductiveConv Inductive {..} = Kernames.Coq_mkInd (kerNameConv indMInd) (natConv indInd)

projectionConv :: Projection -> Kernames.Coq_projection
projectionConv ProjectionIdent {..} =
  Kernames.Coq_mkProjection (inductiveConv projInd) (natConv projNPars) (natConv projArg)

nameConv :: Name -> BasicAst.Coq_name
nameConv Anon = BasicAst.Coq_nAnon
nameConv (Named i) = BasicAst.Coq_nNamed $ identConv $ i

typeConv :: Type -> ExAst.Coq_box_type
typeConv TBox = ExAst.TBox
typeConv TAny = ExAst.TAny
typeConv (TArr t1 t2) = ExAst.TArr (typeConv t1) (typeConv t2)
typeConv (TApp t1 t2) = ExAst.TApp (typeConv t1) (typeConv t2)
typeConv (TVar i) = ExAst.TVar $ natConv i
typeConv (TInd ind) = ExAst.TInd $ inductiveConv $ ind
typeConv (TConst kn) = ExAst.TConst $ kerNameConv $ kn

typeVarInfoConv :: TypeVarInfo -> ExAst.Coq_type_var_info
typeVarInfoConv TypeVarInfo {..} =
  ExAst.Build_type_var_info (nameConv tvarName) tvarIsArity tvarIsLogical tvarIsSort

defConv :: (t -> t') -> Def t -> EAst.Coq_def t'
defConv f Def {..} =
  EAst.Build_def (nameConv dName) (f dBody) (natConv dArgs)

mFixpointConv :: MFixpoint -> EAst.Coq_mfixpoint EAst.Coq_term
mFixpointConv l = map (defConv termConv) l

int64Conv :: Int64 -> PrimInt63.Coq_int
int64Conv i =
  if i <= 4611686018427387903 then i else error "invalid 63-bit integer"

primValueConv :: (PrimValue Term) -> EPrimitive.Coq_prim_val EAst.Coq_term
primValueConv (PInt i) =
  Specif.Coq_existT Primitive.Coq_primInt (EPrimitive.Coq_primIntModel $ int64Conv $ i)
primValueConv (PFloat f) =
  Specif.Coq_existT Primitive.Coq_primFloat (EPrimitive.Coq_primFloatModel f)
primValueConv (PString s) =
  Specif.Coq_existT Primitive.Coq_primString (EPrimitive.Coq_primStringModel s)
primValueConv (PArray x xs) =
  Specif.Coq_existT Primitive.Coq_primArray
    (EPrimitive.Coq_primArrayModel
      (EPrimitive.Build_array_model (termConv x) (termListConv xs)))

termListConv :: [Term] -> [EAst.Coq_term]
termListConv xs = map termConv xs

branchesConv :: [([Name], Term)] -> [([BasicAst.Coq_name], EAst.Coq_term)]
branchesConv xs =
  map (\x -> (map nameConv (fst x), termConv $ snd $ x)) xs

termConv :: Term -> EAst.Coq_term
termConv (LBox) = EAst.Coq_tBox
termConv (LRel i) = EAst.Coq_tRel $ natConv $ i
termConv (LVar i) = EAst.Coq_tVar $ identConv $ i
termConv (LEvar i ts) = EAst.Coq_tEvar (natConv i) (termListConv ts)
termConv (LLambda n t) = EAst.Coq_tLambda (nameConv n) (termConv t)
termConv (LLetIn n t1 t2) =
  EAst.Coq_tLetIn (nameConv n) (termConv t1) (termConv t2)
termConv (LApp t1 t2) = EAst.Coq_tApp (termConv t1) (termConv t2)
termConv (LConst kn) = EAst.Coq_tConst (kerNameConv kn)
termConv (LConstruct ind i ts) =
  EAst.Coq_tConstruct (inductiveConv ind) (natConv i) (termListConv ts)
termConv (LCase ind i t brs) =
  EAst.Coq_tCase (inductiveConv ind, natConv i) (termConv t) (branchesConv brs)
termConv (LProj pr t) = EAst.Coq_tProj (projectionConv pr) (termConv t)
termConv (LFix m i) = EAst.Coq_tFix (mFixpointConv m) (natConv i)
termConv (LCoFix m i) = EAst.Coq_tCoFix (mFixpointConv m) (natConv i)
termConv (LPrim p) = EAst.Coq_tPrim $ primValueConv $ p
termConv (LLazy t) = EAst.Coq_tLazy $ termConv $ t
termConv (LForce t) = EAst.Coq_tForce $ termConv $ t

allowedElimsConv :: AllowedElims -> Universes0.Coq_allowed_eliminations
allowedElimsConv IntoSProp = Universes0.IntoSProp
allowedElimsConv IntoPropSProp = Universes0.IntoPropSProp
allowedElimsConv IntoSetPropSProp = Universes0.IntoSetPropSProp
allowedElimsConv IntoAny = Universes0.IntoAny

recursivityKindConv :: RecursivityKind -> BasicAst.Coq_recursivity_kind
recursivityKindConv Finite = BasicAst.Finite
recursivityKindConv CoFinite = BasicAst.CoFinite
recursivityKindConv BiFinite = BasicAst.BiFinite


constructorBodyConvTyped :: Target t -> ConstructorBody t -> ((Kernames.Coq_ident, [(BasicAst.Coq_name, ExAst.Coq_box_type)]), Datatypes.Coq_nat)
constructorBodyConvTyped ToUntyped _ = error ""
constructorBodyConvTyped ToTyped Constructor{..} =
  ((identConv cstrName, map (\x -> (nameConv $ fst x, typeConv $ snd x)) (getTyped cstrTypes)), natConv cstrArgs)

constructorBodyConvUntyped :: Target t -> ConstructorBody t -> EAst.Coq_constructor_body
constructorBodyConvUntyped ToTyped _ = error ""
constructorBodyConvUntyped ToUntyped Constructor{..} =
  EAst.Coq_mkConstructor (identConv cstrName) (natConv cstrArgs)


projectionBodyConvTyped :: Target t -> ProjectionBody t -> (Kernames.Coq_ident, ExAst.Coq_box_type)
projectionBodyConvTyped ToUntyped _ = error ""
projectionBodyConvTyped ToTyped Projection {..} =
  (identConv projName, typeConv $ getTyped projType)

projectionBodyConvUntyped :: Target t -> ProjectionBody t -> EAst.Coq_projection_body
projectionBodyConvUntyped ToTyped _ = error ""
projectionBodyConvUntyped ToUntyped Projection {..} = identConv projName


oneInductiveBodyConvTyped :: Target t -> OneInductiveBody t -> ExAst.Coq_one_inductive_body
oneInductiveBodyConvTyped ToUntyped _ = error ""
oneInductiveBodyConvTyped ToTyped OneInductive {..} =
  ExAst.Build_one_inductive_body
    (identConv indName)
    indPropositional
    (allowedElimsConv indKElim)
    (map typeVarInfoConv (getTyped indTypeVars))
    (map (constructorBodyConvTyped ToTyped) indCtors)
    (map (projectionBodyConvTyped ToTyped) indProjs)

oneInductiveBodyConvUntyped :: Target t -> OneInductiveBody t -> EAst.Coq_one_inductive_body
oneInductiveBodyConvUntyped ToTyped _ = error ""
oneInductiveBodyConvUntyped ToUntyped OneInductive {..} =
  EAst.Build_one_inductive_body
    (identConv indName)
    indPropositional
    (allowedElimsConv indKElim)
    (map (constructorBodyConvUntyped ToUntyped) indCtors)
    (map (projectionBodyConvUntyped ToUntyped) indProjs)


mutualInductiveBodyConvTyped :: Target t -> MutualInductiveBody t -> ExAst.Coq_mutual_inductive_body
mutualInductiveBodyConvTyped ToUntyped _ = error ""
mutualInductiveBodyConvTyped ToTyped MutualInductive {..} =
  ExAst.Build_mutual_inductive_body
    (recursivityKindConv indFinite)
    (natConv indPars)
    (map (oneInductiveBodyConvTyped ToTyped) indBodies)

mutualInductiveBodyConvUntyped :: Target t -> MutualInductiveBody t -> EAst.Coq_mutual_inductive_body
mutualInductiveBodyConvUntyped ToTyped _ = error ""
mutualInductiveBodyConvUntyped ToUntyped MutualInductive {..} =
  EAst.Build_mutual_inductive_body
    (recursivityKindConv indFinite)
    (natConv indPars)
    (map (oneInductiveBodyConvUntyped ToUntyped) indBodies)


constantBodyConvTyped :: Target t -> ConstantBody t -> ExAst.Coq_constant_body
constantBodyConvTyped ToUntyped _ = error ""
constantBodyConvTyped ToTyped ConstantBody {..} =
  let cst = (getTyped cstType) in
  ExAst.Build_constant_body
    (map nameConv $ fst cst, typeConv $ snd cst)
    (fmap termConv cstBody)

constantBodyConvUntyped :: Target t -> ConstantBody t -> EAst.Coq_constant_body
constantBodyConvUntyped ToTyped _ = error ""
constantBodyConvUntyped ToUntyped ConstantBody {..} = fmap termConv cstBody


globalDeclConvTyped :: Target t -> GlobalDecl t -> ExAst.Coq_global_decl
globalDeclConvTyped ToUntyped _ = error ""
globalDeclConvTyped ToTyped gd =
  case gd of
    ConstantDecl a ->
      ExAst.ConstantDecl $ (constantBodyConvTyped ToTyped) a
    InductiveDecl a ->
      ExAst.InductiveDecl $ (mutualInductiveBodyConvTyped ToTyped) a
    TypeAliasDecl a ->
      ExAst.TypeAliasDecl $ fmap (\x -> (map typeVarInfoConv $ fst x, typeConv $ snd x)) a

globalDeclConvUntyped :: Target t -> GlobalDecl t -> EAst.Coq_global_decl
globalDeclConvUntyped ToTyped _ = error ""
globalDeclConvUntyped ToUntyped gd =
  case gd of
    ConstantDecl a ->
      EAst.ConstantDecl $ (constantBodyConvUntyped ToUntyped) a
    InductiveDecl a ->
      EAst.InductiveDecl $ (mutualInductiveBodyConvUntyped ToUntyped) a


globalEnvConvTyped :: Target t -> GlobalEnv t -> ExAst.Coq_global_env
globalEnvConvTyped ToUntyped _ = error ""
globalEnvConvTyped ToTyped (GlobalEnv env) =
  map (\x -> ((kerNameConv $ fst $ x, True), (globalDeclConvTyped ToTyped) $ snd $ x)) env

globalEnvConvUntyped :: Target t -> GlobalEnv t -> EAst.Coq_global_declarations
globalEnvConvUntyped ToTyped _ = error ""
globalEnvConvUntyped ToUntyped (GlobalEnv env) =
  map (\x -> (kerNameConv $ fst x, (globalDeclConvUntyped ToUntyped) $ snd x)) env


lBoxModuleConv :: Target t -> LBoxModule t -> PAst.PAst
lBoxModuleConv ToUntyped LBoxModule{..} =
  -- Lambda Box only supports one main function so we just take the first element of lboxMain
  PAst.Untyped (globalEnvConvUntyped ToUntyped lboxEnv) (Just $ EAst.Coq_tConst $ kerNameConv $ NEL.head $ getUntyped $ lboxMain)
lBoxModuleConv ToTyped LBoxModule{..} =
  PAst.Typed (globalEnvConvTyped ToTyped lboxEnv) Nothing
