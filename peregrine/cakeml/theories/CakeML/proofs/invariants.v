
From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
From CakeML Require Import bigstep.
From CakeML Require Import smallstep.
From CakeML Require Import smallstep_rel.
Import ListNotations.

(* --- auxiliary relation for proving big/small step equivalence --- *)

Inductive evaluate_ctxt (env:Sem_env val) : ctxt_frame -> val -> result->Prop:=
	| evaluate_ctxt_Raise v :
		evaluate_ctxt env (Craise tt) v (Rerr (Rraise v))
	| evaluate_ctxt_Handle pes v:
		evaluate_ctxt env (Chandle tt pes) v (Rval v)
	
	| evaluate_ctxt_App_err es err vs op v:
		evaluate_list env es (Rerr_l err) ->
		evaluate_ctxt env (Capp op vs tt es) v (Rerr err)
	
	| evaluate_ctxt_App  env' es vs vs1 e op bv v: 
		evaluate_list env es (Rval_l vs) -> 
		do_opapp (rev vs ++ [v] ++ vs1) = Some (env',e) ->
		opClass op FunApp ->
		evaluate env' e bv ->
		evaluate_ctxt env (Capp op vs1 tt es) v bv

	| evaluate_ctxt_Let n e2 va bv:
		evaluate {| v:= nsOptBind n va env.(v val) ; c:= env.(c val)|} e2 bv ->
		evaluate_ctxt env (Clet n tt e2) va bv

	| evaluate_ctxt_Cmat v pes bv err_v:
		evaluate_match env v pes err_v bv -> 
		evaluate_ctxt env (Cmat tt pes err_v) v bv

	| evaluate_ctxt_Cmat_check v pes bv err_v:
		evaluate_match env v pes err_v bv -> 
		can_pmatch_all env.(c val) (map fst pes) v = true ->
		evaluate_ctxt env (Cmat_check tt pes err_v) v bv

	| evaluate_ctxt_Ccon cn vs vs' es v v':
		do_con_check env.(c val) cn ((List.length vs)+1+(List.length es)) = true->
		build_conv env.(c val) cn (rev vs' ++ [v] ++ vs) = Some v' ->
		evaluate_list env es (Rval_l vs') ->
		evaluate_ctxt env (Ccon cn vs tt es) v (Rval v')
	
	| evaluate_ctxt_Ccon_err cn vs es v err :
		do_con_check env.(c val) cn ((List.length vs)+1+(List.length es)) = true ->
		evaluate_list env es (Rerr_l err) ->
		evaluate_ctxt env (Ccon cn vs tt es) v (Rerr err).

Inductive evaluate_ctxts : (list ctxt) -> result -> result -> Prop :=
	| evaluate_ctxts_nil res : 
		evaluate_ctxts [] res res
	
	| evaluate_ctxts_cons env c v res cs bv: 
		evaluate_ctxt env c v res ->
		evaluate_ctxts cs res bv ->
		evaluate_ctxts ((c,env)::cs) (Rval v) bv
	
	| evaluate_ctxts_handle env v pes res1 res2 cs :
		evaluate_match env v pes v res1 ->
		can_pmatch_all env.(c val) (map fst pes) v = true ->
		evaluate_ctxts cs res1 res2 ->
		evaluate_ctxts ((Chandle tt pes,env)::cs) (Rerr (Rraise v)) res2

	| evaluate_ctxts_not_handle c0 cs err bv: 
		evaluate_ctxts cs (Rerr err) bv ->
		not_handle c0 = true -> 
		evaluate_ctxts (c0::cs) (Rerr err) bv. 

Inductive evaluate_state : small_state -> result -> Prop :=
	| evaluate_state_exp env e res c bv : 
		evaluate env e res ->
		evaluate_ctxts c res bv ->
		evaluate_state (env, Exp e, c) bv
		
	|  evaluate_state_val env v c bv : 
		evaluate_ctxts c (Rval v) bv ->
		evaluate_state (env, Val v, c) bv

	| evaluate_state_Exn env v c bv : 
		evaluate_ctxts c (Rerr (Rraise v)) bv ->
		evaluate_state (env, Exn v, c) bv.