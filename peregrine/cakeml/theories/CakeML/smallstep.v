From Stdlib Require Import Lia List Peano Nat.
From Stdlib Require Import Strings.String.
From CakeML Require Import ast.
From CakeML Require Import namespace.
From CakeML Require Import semanticPrimitives.
From CakeML Require Import functions.
Import ListNotations.


Inductive exp_val_exn :=
| Exp (e:exp)
| Val (v:val)
| Exn (v:val).

Inductive ctxt_frame :=
| Capp (o:op) (v:list val) (u:unit) (e:list exp)
| Clet (n:option varN) (u:unit) (e:exp)
| Cmat_check (u:unit) (ps: list (pat*exp)) (err_v:val)
| Cmat (u:unit) (ps: list (pat*exp)) (bind_exn_v:val)
| Ccon (n: option id) (vs:list val) (u:unit) (es : list exp)
| Craise (u:unit)
| Chandle (u:unit) (l:list (pat*exp)).


Definition ctxt := ((ctxt_frame)*(Sem_env val))%type.

Definition small_state := ((Sem_env val)*(exp_val_exn)*(list ctxt))%type.

Inductive e_step_result := 
Estep (s:small_state)
|Estuck
|Eabort.

Definition push (env:Sem_env val) (e:exp) (c':ctxt_frame) (cs:list ctxt):e_step_result :=
Estep( (env, Exp e, ((c',env)::cs))).

Definition return_def (env:Sem_env val) (v:val) (c:list ctxt):e_step_result:=
Estep(env,Val v, c).

Definition application (o:op) (env:Sem_env val) (vs:list val) (c:list ctxt):=
	match getOpClass o with
	|FunApp => 
		match do_opapp vs with
		|None => Eabort
		|Some (env',e) => Estep (env', Exp e, c )
		end
	end.

Definition continue (va:val) (cs:list ctxt):e_step_result:=
	match cs with
	| [] => Estuck
	| (Capp o vs tt [],env)::c => application o env (va::vs) c
	| (Capp o vs tt (e::es),env)::c => push env e (Capp o (va::vs) tt es) c
	| (Clet n tt e,env)::c0 => Estep ({|v := (nsOptBind n va env.(v val)) ; c:= env.(c val)|}, Exp e, c0)
	| (Cmat_check tt pes err_v,env)::c0 =>
		if can_pmatch_all env.(c val) (map fst pes) va then 
			Estep (env,Val va,(Cmat tt pes err_v,env)::c0) 
		else Eabort
	| (Cmat tt [] err_v,env)::c0 => 
		Estep (env, Exn err_v,c0)
	| (Cmat tt ((p,e)::pes) err_v,env)::c0 =>  
		if ALL_DISTINCT conN (fun x y => negb (x=?y)%string) (pat_bindings p []) then
			match pmatch env.(c val) p va [] with
			|Match_type_error _ => Eabort
			|No_match _ => Estep (env, Val va, (Cmat tt pes err_v,env)::c0)
			|Match _ env' => Estep ({| v:= nsAppend (alist_to_ns env') env.(v val); c:= env.(c val) |},Exp e, c0)
			end
		else 
			Eabort
	| (Ccon n vs tt [],env)::c0 => 
		if do_con_check env.(c val) n ((List.length vs) + 1) then 
			match build_conv env.(c val) n (va::vs) with
			|None => Eabort
			|Some v' => return_def env v' c0  
			end
		else
			Eabort
	| (Ccon n vs tt (e::es),env) :: c0 => 
		if do_con_check env.(c val) n ((List.length vs) + 1+1+(List.length es)) then 
			push env e (Ccon n (va::vs) tt es) c0
		else
			Eabort
	| (Craise tt,env)::c0 => 
		Estep (env, Exn va, c0)
	| (Chandle tt pes,env)::c0 =>
		return_def env va c0
	end.


Definition e_step (s1 :small_state):e_step_result:=
	match s1 with
	| (env,ev,c0) =>
		match ev  with
		|Val v => continue v c0
		|Exp e => 
			match e with
			| Lit l => return_def env (Litv l) c0
			|Var n => 
				match nsLookup val env.(v val) n with
				| None => Eabort
				| Some v => return_def env v c0
				end
			| Fun n e => return_def env (Closure env n e) c0
			| App o es =>
				match rev es with
				| [] => application o env [] c0 
				| (e::eq) => push env e (Capp o [] tt eq) c0
				end
			| Let n e1 e2 => push env e1 (Clet n tt e2) c0
			| Con n es => 
				if do_con_check env.(c val) n (List.length es) then
                match rev es with
                |[] =>
                    match build_conv env.(c val) n [] with
                        | None => Eabort 
                        | Some va => return_def env va c0
                    end
                | e::es' =>
                    push env e (Ccon n [] tt  es') c0
                end
            else
                Eabort 
			| Mat e pes => push env e (Cmat_check tt pes bind_exn_v) c0
			| Letrec funs e =>
				if ALL_DISTINCT varN (fun x y => negb (x=?y)%string) (map (fun '(x,_,_)=>x) funs) then
					Estep ({| v:= (build_rec_env funs env env.(v val)) ; c:= env.(c val) |},Exp e, c0)
				else
					Eabort
			| Raise e => 
				push env e (Craise tt) c0
			| Handle e pes => 
				push env e (Chandle tt pes) c0
			end
		| Exn v => 
			match c0 with 
			| [] => 
				Estuck
			| (Chandle tt pes, env') :: c0' =>
				Estep (env, Val v, (Cmat_check tt pes v, env')::c0')
			| _ :: c0' => Estep (env, Exn v, c0')
			end
		end
	end.

Inductive e_step_reln (st1:small_state) (st2:small_state):Prop:= (* st1 ~ st2 if st2 is reached after one step from st1*)
	e_step_reln_def: (e_step st1) = Estep st2 -> e_step_reln st1 st2.


Inductive small_eval (env:Sem_env val) (e:exp) (c:list ctxt) (r:result):Prop :=
	|value env' v: (r = Rval v)/\(RTC small_state e_step_reln (env,Exp e,c) (env',Val v,[])) -> small_eval env e c r
	|abort env' e' c' err: 
		(r = Rerr err) -> 
		(RTC ((Sem_env val)*(exp_val_exn)*(list ctxt)) e_step_reln (env,Exp e,c) (env',Exp e',c') /\ e_step (env',Exp e',c') = Eabort ) ->
		small_eval env e c r.

Inductive e_diverges (env:Sem_env val) (e:exp):Prop :=
|e_diverges_def (env':Sem_env val) (e':exp) (c':list ctxt) :
	RTC small_state e_step_reln (env,Exp e,[]) (env',Exp e',c') ->
		(exists (env'':Sem_env val) (e'':exp) (c'':list ctxt), e_step_reln (env',Exp e',c') (env'',Exp e'',c'')) ->
			e_diverges env e.