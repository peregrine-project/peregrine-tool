  From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
From CakeML Require Import smallstep.
Import ListNotations.

Definition not_handle (c:ctxt_frame*(Sem_env val)):bool :=
	match c with 
	| (Chandle tt _,_)	=> false
	| (_,_) => true
	end.

Inductive e_step_rel : small_state -> small_state -> Prop :=
	| e_step_var env c n v1 :
		nsLookup val env.(v val) n = Some v1 ->  
		e_step_rel (env,Exp (Var n),c)  (env,Val v1,c)
	
	| e_step_lit env l c:
		e_step_rel (env,Exp (Lit l),c) (env,Val (Litv l),c)

	| e_step_Fun env c n e :
		e_step_rel (env,Exp (Fun n e),c) (env,Val (Closure env n e),c)

	| e_step_App env c o e es: 
		e_step_rel (env,Exp( App o (rev (e::es))),c) (env,Exp e,(Capp o [] tt es,env)::c)

	| e_step_let env n e1 e2 c: e_step_rel (env,Exp ( Let n e1 e2), c) (env, Exp e1, (Clet n tt e2,env)::c )

	| e_step_Con_nil env n va c0: 
		do_con_check env.(c val) n 0 = true ->
		build_conv env.(c val) n [] = Some va ->
		e_step_rel (env,Exp (Con n []),c0) (env,Val va,c0)

	| e_step_Con_cons env n e c0 es':  
		do_con_check env.(c val) n (List.length (rev (e::es'))) = true ->
		e_step_rel (env,Exp (Con n (rev (e::es'))) ,c0) (env,Exp e,(Ccon n [] tt es',env)::c0)

	| e_step_Mat env e pes c0:
		e_step_rel (env,Exp (Mat e pes),c0) (env,Exp e,(Cmat_check tt pes bind_exn_v,env)::c0)
	
	| e_step_Letrec env funs e c0: 
		List.NoDup (map (fun '(x,_,_)=>x) funs) ->
		e_step_rel (env,Exp (Letrec funs e),c0) ( {| v:= (build_rec_env funs env env.(v val)) ; c:= env.(c val) |},Exp e,c0)

	| e_step_Raise env e  c0: 
		e_step_rel (env,Exp (Raise e),c0) (env, Exp e,(Craise tt,env)::c0)

	| e_step_Handle env e pes c0:
		e_step_rel (env,Exp (Handle e pes),c0) (env, Exp e,(Chandle tt pes,env)::c0)

	| e_step_val1 env env' env'' v vs o c e:
		do_opapp (v::vs) = Some (env'',e) ->
		e_step_rel (env,Val v,(Capp o vs tt [],env')::c) (env'',Exp e,c) 

	| e_step_val2 env env' c v o vs e es:
		e_step_rel (env,Val v,(Capp o vs tt (e::es),env')::c) (env', Exp e, (Capp o (v::vs) tt es,env')::c)
		
	| e_step_val_let env env'  va n e c0: 
		e_step_rel (env, Val va, (Clet n tt e, env')::c0) ({|v := nsOptBind n va env'.(v val) ; c:= env'.(c val)|}, Exp e , c0)
		
	| e_step_Cmat_NM p va env e pes c0 env' err_v:
		List.NoDup (pat_bindings p []) ->
		pmatch env'.(c val) p va [] = No_match env_l ->
		e_step_rel (env, Val va,(Cmat tt ((p,e)::pes) err_v,env')::c0) (env', Val va, (Cmat tt pes err_v,env')::c0)
	
	| e_step_Cmat_M p va env e pes c0 env' env'' err_v:
		List.NoDup (pat_bindings p []) ->
		pmatch env'.(c val) p va [] = Match env_l env'' ->
		e_step_rel (env, Val va,(Cmat tt ((p,e)::pes) err_v,env')::c0) ({| v:= nsAppend (alist_to_ns env'') env'.(v val); c:= env'.(c val) |}, Exp e,c0)
	
	| e_step_Cmat_nil env va err_v env' c0:
		e_step_rel (env, Val va, (Cmat tt [] err_v,env')::c0) (env', Exn err_v,c0)

	| e_step_Cmat_check env va pes c0 env' err_v:
		can_pmatch_all env'.(c val) (map fst pes) va = true ->
		e_step_rel (env, Val va,(Cmat_check tt pes err_v,env')::c0) (env', Val va, (Cmat tt pes err_v,env')::c0)
	
	| e_step_Ccon_nil env va v' n vs c0 env' :
		do_con_check env'.(c val) n ((List.length vs) + 1) = true ->
		build_conv env'.(c val) n (va::vs) = Some v' ->
		e_step_rel (env, Val va,(Ccon n vs tt [],env')::c0) (env',Val v', c0)
		
	|e_step_Ccon_cons env va n vs c0 e es env' :
		do_con_check env'.(c val) n ((List.length vs) + 1+1+(List.length es)) = true ->
		e_step_rel (env, Val va, (Ccon n vs tt (e::es),env')::c0) (env', Exp e, (Ccon n (va::vs) tt es,env')::c0)
	
	| e_step_CRaise env env' va c0:
		e_step_rel (env, Val va, (Craise tt,env')::c0) (env', Exn va, c0)

	| e_step_Chandle env va pes env' c0 :
		e_step_rel (env, Val va, (Chandle tt pes, env')::c0) (env', Val va, c0)

	| e_step_Exn_H env va pes env' c0:
		e_step_rel (env, Exn va, (Chandle tt pes, env') :: c0) (env, Val va, (Cmat_check tt pes va, env')::c0)
	
	|e_step_Exn_NH	env va c0 cs:
		not_handle c0 = true ->
		e_step_rel (env, Exn va, c0::cs) (env, Exn va, cs).

Definition to_small_result (v:result):exp_val_exn:=
	match v with
	| Rval va => Val va
	| Rerr (Rraise va) => Exn va
	end.

Inductive small_eval_list (env:Sem_env val) :(list exp)-> Sem_env val ->list_result-> Prop := 
	|small_eval_nil : 
		small_eval_list env [] env (Rval_l [])

	|small_eval_cons  env' env'' e v es vs: 
		RTC small_state e_step_rel (env,Exp e,[]) (env',Val v,[]) -> 
		small_eval_list env es env'' (Rval_l vs) ->
		small_eval_list env (e::es) env'' (Rval_l (v::vs)) 

	| small_eval_err  env' e es err:
		RTC small_state e_step_rel (env,Exp e,[]) (env',Exn err,[]) -> 
		small_eval_list env (e::es) env' (Rerr_l (Rraise err)) 

	|small_eval_cons_err  env' env'' e v es err:
		RTC small_state e_step_rel (env,Exp e,[]) (env',Val v,[]) -> 
		small_eval_list env es env'' (Rerr_l err) ->
		small_eval_list env (e::es) env'' (Rerr_l err). 


Inductive small_eval_match (env:Sem_env val): val -> list(pat*exp)->Sem_env val->val->result->Prop:=
	| small_eval_match_M e p pes va bv bv' env' env'' err_v:
		ALL_DISTINCT_rel conN  (pat_bindings p []) -> 
		pmatch env.(c val) p va [] = Match env_l env'  ->
		to_small_result bv = bv' ->
		RTC small_state e_step_rel ({| v:= nsAppend (alist_to_ns env') env.(v val); c:= env.(c val) |}, Exp e,[]) (env'',bv',[]) ->
		small_eval_match env va ((p,e)::pes) env'' err_v bv

	| small_eval_match_NM e p pes va bv env' err_v:
		ALL_DISTINCT_rel conN  (pat_bindings p []) -> 
		pmatch env.(c val) p va [] = No_match env_l  ->
		small_eval_match env va pes env' err_v bv ->
		small_eval_match env va ((p,e)::pes) env' err_v bv
		
	| small_eval_match_err va err_v: 
		small_eval_match env va [] env err_v (Rerr (Rraise err_v)).