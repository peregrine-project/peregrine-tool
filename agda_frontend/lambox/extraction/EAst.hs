module EAst where

import qualified Prelude
import qualified BasicAst
import qualified Datatypes
import qualified EPrimitive
import qualified Kernames
import qualified Universes0

data Coq_def term =
   Build_def BasicAst.Coq_name term Datatypes.Coq_nat

dname :: (Coq_def a1) -> BasicAst.Coq_name
dname d =
  case d of {
   Build_def dname0 _ _ -> dname0}

dbody :: (Coq_def a1) -> a1
dbody d =
  case d of {
   Build_def _ dbody0 _ -> dbody0}

rarg :: (Coq_def a1) -> Datatypes.Coq_nat
rarg d =
  case d of {
   Build_def _ _ rarg0 -> rarg0}

type Coq_mfixpoint term = ([]) (Coq_def term)

data Coq_term =
   Coq_tBox
 | Coq_tRel Datatypes.Coq_nat
 | Coq_tVar Kernames.Coq_ident
 | Coq_tEvar Datatypes.Coq_nat (([]) Coq_term)
 | Coq_tLambda BasicAst.Coq_name Coq_term
 | Coq_tLetIn BasicAst.Coq_name Coq_term Coq_term
 | Coq_tApp Coq_term Coq_term
 | Coq_tConst Kernames.Coq_kername
 | Coq_tConstruct Kernames.Coq_inductive Datatypes.Coq_nat (([]) Coq_term)
 | Coq_tCase ((,) Kernames.Coq_inductive Datatypes.Coq_nat) Coq_term 
 (([]) ((,) (([]) BasicAst.Coq_name) Coq_term))
 | Coq_tProj Kernames.Coq_projection Coq_term
 | Coq_tFix (Coq_mfixpoint Coq_term) Datatypes.Coq_nat
 | Coq_tCoFix (Coq_mfixpoint Coq_term) Datatypes.Coq_nat
 | Coq_tPrim (EPrimitive.Coq_prim_val Coq_term)
 | Coq_tLazy Coq_term
 | Coq_tForce Coq_term

data Coq_constructor_body =
   Coq_mkConstructor Kernames.Coq_ident Datatypes.Coq_nat

cstr_name :: Coq_constructor_body -> Kernames.Coq_ident
cstr_name c =
  case c of {
   Coq_mkConstructor cstr_name0 _ -> cstr_name0}

cstr_nargs :: Coq_constructor_body -> Datatypes.Coq_nat
cstr_nargs c =
  case c of {
   Coq_mkConstructor _ cstr_nargs0 -> cstr_nargs0}

type Coq_projection_body =
  Kernames.Coq_ident
  -- singleton inductive, whose constructor was mkProjection
  
proj_name :: Coq_projection_body -> Kernames.Coq_ident
proj_name p =
  p

data Coq_one_inductive_body =
   Build_one_inductive_body Kernames.Coq_ident Prelude.Bool Universes0.Coq_allowed_eliminations 
 (([]) Coq_constructor_body) (([]) Coq_projection_body)

ind_name :: Coq_one_inductive_body -> Kernames.Coq_ident
ind_name o =
  case o of {
   Build_one_inductive_body ind_name0 _ _ _ _ -> ind_name0}

ind_propositional :: Coq_one_inductive_body -> Prelude.Bool
ind_propositional o =
  case o of {
   Build_one_inductive_body _ ind_propositional0 _ _ _ -> ind_propositional0}

ind_kelim :: Coq_one_inductive_body -> Universes0.Coq_allowed_eliminations
ind_kelim o =
  case o of {
   Build_one_inductive_body _ _ ind_kelim0 _ _ -> ind_kelim0}

ind_ctors :: Coq_one_inductive_body -> ([]) Coq_constructor_body
ind_ctors o =
  case o of {
   Build_one_inductive_body _ _ _ ind_ctors0 _ -> ind_ctors0}

ind_projs :: Coq_one_inductive_body -> ([]) Coq_projection_body
ind_projs o =
  case o of {
   Build_one_inductive_body _ _ _ _ ind_projs0 -> ind_projs0}

data Coq_mutual_inductive_body =
   Build_mutual_inductive_body BasicAst.Coq_recursivity_kind Datatypes.Coq_nat 
 (([]) Coq_one_inductive_body)

ind_finite :: Coq_mutual_inductive_body -> BasicAst.Coq_recursivity_kind
ind_finite m =
  case m of {
   Build_mutual_inductive_body ind_finite0 _ _ -> ind_finite0}

ind_npars :: Coq_mutual_inductive_body -> Datatypes.Coq_nat
ind_npars m =
  case m of {
   Build_mutual_inductive_body _ ind_npars0 _ -> ind_npars0}

ind_bodies :: Coq_mutual_inductive_body -> ([]) Coq_one_inductive_body
ind_bodies m =
  case m of {
   Build_mutual_inductive_body _ _ ind_bodies0 -> ind_bodies0}

type Coq_constant_body =
  Prelude.Maybe Coq_term
  -- singleton inductive, whose constructor was Build_constant_body
  
cst_body :: Coq_constant_body -> Prelude.Maybe Coq_term
cst_body c =
  c

data Coq_global_decl =
   ConstantDecl Coq_constant_body
 | InductiveDecl Coq_mutual_inductive_body

type Coq_global_declarations =
  ([]) ((,) Kernames.Coq_kername Coq_global_decl)

