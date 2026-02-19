From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
Import ListNotations.

(* Bigstep semantic *)


(* https://github.com/CakeML/cakeml/blob/master/semantics/alt_semantics/bigStepScript.sml#L68 *)
Inductive evaluate (env : Sem_env val) : exp -> result -> Prop := 

| evaluate_raise e v :
	evaluate env e (Rval v) ->
	evaluate env (Raise e) (Rerr (Rraise v)) 

| evaluate_raise_err e err:
	evaluate env e (Rerr err) ->
	evaluate env (Raise e) (Rerr err) 

| evaluate_lit l:
	evaluate env (Lit l) (Rval (Litv l))

| evaluate_handle e v pes :
	evaluate env e (Rval v) ->
	evaluate env (Handle e pes) (Rval v)

| evaluate_handle_err e pes v bv :
	evaluate env e (Rerr (Rraise v)) ->
	evaluate_match env v pes v bv ->
	can_pmatch_all env.(c val) (map fst pes) v = true ->
	evaluate env (Handle e pes) bv

| evaluate_Var n v1 :
	nsLookup val (env.(v val)) n = Some v1 ->
	evaluate env (Var n) (Rval v1)

| evaluate_Fun n e :
	evaluate env (Fun n e) (Rval (Closure env n e))

| evaluate_App op es bv vs env' e :
	evaluate_list env (rev es) (Rval_l vs) ->
	do_opapp (rev vs) = Some (env', e) ->
	evaluate env' e  bv ->
	(opClass op FunApp) ->
	evaluate env (App op es) bv

| evaluate_App_err1 op es err :
	evaluate_list env (rev es) (Rerr_l err) ->
	evaluate env (App op es) (Rerr err)

| evaluate_Let n e1 e2 va bv : 
	evaluate env e1 (Rval va) ->
	evaluate ({|v:=( nsOptBind n va env.(v val)); c:= env.(c val) |}) e2 bv ->
	evaluate env (Let n e1 e2) bv

| evaluate_Let_err n e1 e2 err : 
	evaluate env e1 (Rerr err) ->
	evaluate env (Let n e1 e2) (Rerr err)

| evaluate_Con cn es vs v :
	do_con_check env.(c val) cn (List.length es) = true ->
	build_conv env.(c val) cn (rev vs) = Some v ->
	evaluate_list env (rev es) (Rval_l vs) ->
	evaluate env (Con cn es) (Rval v)

| evaluate_Con_Rerr cn es err:
	do_con_check env.(c val) cn (List.length es) = true ->
	evaluate_list env (rev es) (Rerr_l err) ->
	evaluate env (Con cn es) (Rerr err)

| evaluate_Mat e pes v bv :
	evaluate env e (Rval v) ->
	evaluate_match env v pes bind_exn_v bv ->
	can_pmatch_all env.(c val) (map fst pes) v = true ->
	evaluate env (Mat e pes)  bv

| evaluate_Mat_err e pes err :
	evaluate env e (Rerr err) ->
	evaluate env (Mat e pes) (Rerr err)


| evaluate_Letrec funs e bv:
	ALL_DISTINCT_rel varN (map (fun '(x,_,_) => x) funs) ->
	evaluate {| v:= (build_rec_env funs env env.(v val)); c:= env.(c val)|} e  bv ->
	evaluate env (Letrec funs e) bv

with evaluate_list (env : Sem_env val) : list exp -> list_result -> Prop :=
| evaluate_nil :
	evaluate_list env [] (Rval_l [])	

| evaluate_cons e es v vs :
	evaluate env e (Rval v) ->
	evaluate_list env es (Rval_l vs) ->
	evaluate_list env (e :: es) (Rval_l (v :: vs))

| evaluate_cons_err1 e es err :
	evaluate env e (Rerr err) ->
	evaluate_list env (e::es) (Rerr_l err)

| evaluate_cons_err2 e es v err :
	evaluate env e (Rval v) ->
	evaluate_list env es (Rerr_l err) ->
	evaluate_list env (e::es) (Rerr_l err)

with evaluate_match (env : Sem_env val) :val-> list (pat*exp) -> val -> result->Prop :=
| evaluate_match_M e p pes va bv env' err_v:
	ALL_DISTINCT_rel conN  (pat_bindings p []) -> 
	pmatch env.(c val) p va [] = Match env_l env'  ->
	evaluate {| v:= nsAppend (alist_to_ns env') env.(v val); c:= env.(c val) |} e bv ->
	evaluate_match env va ((p,e)::pes) err_v bv

| evaluate_match_NM e p pes va bv err_v:
	ALL_DISTINCT_rel conN  (pat_bindings p []) -> 
	pmatch env.(c val) p va [] = No_match env_l ->
	evaluate_match env va (pes) err_v bv ->
	evaluate_match env va ((p,e)::pes) err_v bv

| evaluate_Match_err va err_v:
	evaluate_match env va [] err_v (Rerr (Rraise err_v)).

Scheme evaluate_mut_ind :=  Induction for evaluate Sort Prop
with evaluate_list_mut_ind := Induction for evaluate_list Sort Prop
with evaluate_match_mut_ind := Induction for evaluate_match Sort Prop.

Combined Scheme evaluate_mutual_ind from evaluate_mut_ind, evaluate_list_mut_ind,evaluate_match_mut_ind.

