module ExAst where

import qualified Prelude
import qualified BasicAst
import qualified Datatypes
import qualified EAst
import qualified Kernames
import qualified Universes0

data Coq_box_type =
   TBox
 | TAny
 | TArr Coq_box_type Coq_box_type
 | TApp Coq_box_type Coq_box_type
 | TVar Datatypes.Coq_nat
 | TInd Kernames.Coq_inductive
 | TConst Kernames.Coq_kername

data Coq_constant_body =
   Build_constant_body ((,) (([]) BasicAst.Coq_name) Coq_box_type) (Prelude.Maybe
                                                                   EAst.Coq_term)

cst_type :: Coq_constant_body -> (,) (([]) BasicAst.Coq_name) Coq_box_type
cst_type c =
  case c of {
   Build_constant_body cst_type0 _ -> cst_type0}

cst_body :: Coq_constant_body -> Prelude.Maybe EAst.Coq_term
cst_body c =
  case c of {
   Build_constant_body _ cst_body0 -> cst_body0}

data Coq_type_var_info =
   Build_type_var_info BasicAst.Coq_name Prelude.Bool Prelude.Bool Prelude.Bool

tvar_name :: Coq_type_var_info -> BasicAst.Coq_name
tvar_name t =
  case t of {
   Build_type_var_info tvar_name0 _ _ _ -> tvar_name0}

tvar_is_logical :: Coq_type_var_info -> Prelude.Bool
tvar_is_logical t =
  case t of {
   Build_type_var_info _ tvar_is_logical0 _ _ -> tvar_is_logical0}

tvar_is_arity :: Coq_type_var_info -> Prelude.Bool
tvar_is_arity t =
  case t of {
   Build_type_var_info _ _ tvar_is_arity0 _ -> tvar_is_arity0}

tvar_is_sort :: Coq_type_var_info -> Prelude.Bool
tvar_is_sort t =
  case t of {
   Build_type_var_info _ _ _ tvar_is_sort0 -> tvar_is_sort0}

data Coq_one_inductive_body =
   Build_one_inductive_body Kernames.Coq_ident Prelude.Bool Universes0.Coq_allowed_eliminations 
 (([]) Coq_type_var_info) (([])
                          ((,)
                          ((,) Kernames.Coq_ident
                          (([]) ((,) BasicAst.Coq_name Coq_box_type)))
                          Datatypes.Coq_nat)) (([])
                                              ((,) Kernames.Coq_ident
                                              Coq_box_type))

ind_name :: Coq_one_inductive_body -> Kernames.Coq_ident
ind_name o =
  case o of {
   Build_one_inductive_body ind_name0 _ _ _ _ _ -> ind_name0}

ind_propositional :: Coq_one_inductive_body -> Prelude.Bool
ind_propositional o =
  case o of {
   Build_one_inductive_body _ ind_propositional0 _ _ _ _ ->
    ind_propositional0}

ind_kelim :: Coq_one_inductive_body -> Universes0.Coq_allowed_eliminations
ind_kelim o =
  case o of {
   Build_one_inductive_body _ _ ind_kelim0 _ _ _ -> ind_kelim0}

ind_type_vars :: Coq_one_inductive_body -> ([]) Coq_type_var_info
ind_type_vars o =
  case o of {
   Build_one_inductive_body _ _ _ ind_type_vars0 _ _ -> ind_type_vars0}

ind_ctors :: Coq_one_inductive_body -> ([])
             ((,)
             ((,) Kernames.Coq_ident
             (([]) ((,) BasicAst.Coq_name Coq_box_type))) Datatypes.Coq_nat)
ind_ctors o =
  case o of {
   Build_one_inductive_body _ _ _ _ ind_ctors0 _ -> ind_ctors0}

ind_projs :: Coq_one_inductive_body -> ([])
             ((,) Kernames.Coq_ident Coq_box_type)
ind_projs o =
  case o of {
   Build_one_inductive_body _ _ _ _ _ ind_projs0 -> ind_projs0}

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

data Coq_global_decl =
   ConstantDecl Coq_constant_body
 | InductiveDecl Coq_mutual_inductive_body
 | TypeAliasDecl (Prelude.Maybe ((,) (([]) Coq_type_var_info) Coq_box_type))

type Coq_global_env =
  ([]) ((,) ((,) Kernames.Coq_kername Prelude.Bool) Coq_global_decl)

