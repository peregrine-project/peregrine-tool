From CertiRocq.LambdaANF Require Import cps.
From CertiRocq.LambdaANF Require Import eval.
From CertiRocq.LambdaANF Require Import toplevel.
From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import SerializeLambdaBoxMut.

Import ListNotations.
Local Open Scope bs_scope.



(*
Definition LambdaANF_FullTerm : Type := LambdaANFenv * LambdaANFterm.
Definition LambdaANFterm : Type := cps.exp.
(* exp & val defined in cps *)
Definition LambdaANFenv : Type := eval.prims * prim_env * ctor_env * ctor_tag * ind_tag * name_env * fun_env * eval.env.
Module M := Maps.PTree. (* Compcert maps *)
Definition prim_env := M.t (kername * string (* C definition *) * bool (* tinfo *) * nat (* arity *)).
Definition eval.prims := M.t (list val -> option val).
Definition eval.env := M.t val.
Definition ind_tag  := M.elt.
Definition ctor_tag := M.elt.
Definition ctor_env : Set := M.tree ctor_ty_info.
Definition fun_env : Set := M.tree fun_ty_info.
*)
Instance Serialize_LambdaANF_FullTerm : Serialize LambdaANF_FullTerm :=
  fun x => Atom "TODO".

Definition string_of_LambdaANF_FullTerm (x : LambdaANF_FullTerm) : string :=
  @to_string LambdaANF_FullTerm Serialize_LambdaANF_FullTerm x.
