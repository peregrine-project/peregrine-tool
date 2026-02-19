module Kernames where

import qualified Prelude
import qualified Datatypes
import qualified Bytestring

type Coq_ident = Bytestring.String__Coq_t

type Coq_dirpath = ([]) Coq_ident

data Coq_modpath =
   MPfile Coq_dirpath
 | MPbound Coq_dirpath Coq_ident Datatypes.Coq_nat
 | MPdot Coq_modpath Coq_ident

type Coq_kername = (,) Coq_modpath Coq_ident

data Coq_inductive =
   Coq_mkInd Coq_kername Datatypes.Coq_nat

inductive_mind :: Coq_inductive -> Coq_kername
inductive_mind i =
  case i of {
   Coq_mkInd inductive_mind0 _ -> inductive_mind0}

inductive_ind :: Coq_inductive -> Datatypes.Coq_nat
inductive_ind i =
  case i of {
   Coq_mkInd _ inductive_ind0 -> inductive_ind0}

data Coq_projection =
   Coq_mkProjection Coq_inductive Datatypes.Coq_nat Datatypes.Coq_nat

proj_ind :: Coq_projection -> Coq_inductive
proj_ind p =
  case p of {
   Coq_mkProjection proj_ind0 _ _ -> proj_ind0}

proj_npars :: Coq_projection -> Datatypes.Coq_nat
proj_npars p =
  case p of {
   Coq_mkProjection _ proj_npars0 _ -> proj_npars0}

proj_arg :: Coq_projection -> Datatypes.Coq_nat
proj_arg p =
  case p of {
   Coq_mkProjection _ _ proj_arg0 -> proj_arg0}

