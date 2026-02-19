From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia List Peano Nat.
From CakeML Require Import ast.
From CakeML Require Import functions.
From CakeML Require Import namespace.
Import ListNotations.

Definition env_ctor := namespace modN conN (nat*stamp). 

Definition bind_stamp := ExnStamp 0.

Definition bind_exn_v := Conv (Some bind_stamp) [].


Definition do_con_check (envC:env_ctor) (n_opt: option id) (l:nat):bool :=
	match n_opt with 
	| None => true
	| Some n => 
		match nsLookup ((nat*stamp)%type) envC n with
		| None => false
		| Some (l',_) => l=?l'
		end
	end.

Definition build_conv (envC:env_ctor) (n_opt : option id) (vs : list val):option val:=
	match n_opt with
	| None => Some (Conv None vs)
	| Some n =>
		match  nsLookup ((nat*stamp)%type) envC n with
		| None => None
		| Some (_,stamp) => Some (Conv (Some stamp) vs)
		end
	end.

Inductive list_result :=
	| Rval_l (vs:list val)
	| Rerr_l (e:error_result).

Inductive match_result a :=
| No_match
| Match_type_error
| Match (e:a).


Definition same_type (s0:stamp) (s1:stamp) :=
	match s0,s1 with
	| TypeStamp _ n0, TypeStamp _ n1 => (n0 =? n1)
	| ExnStamp _, ExnStamp _ => true
	| _,_ => false
	
	end.
	
Definition same_ctor (s0:stamp) (s1:stamp) :=
	match s0,s1 with
	| TypeStamp v0 n0, TypeStamp v1 n1 => andb (n0 =? n1) (v0 =? v1)%string
	|  ExnStamp n0, ExnStamp n1 =>  (n0 =? n1)
	| _, _ => false
	end.

Notation env_l := (list (varN*val)).

Fixpoint  pmatch_list_helper (f: env_ctor->pat->val->env_l->match_result (env_l)) envC lp lv env :=
	match lp,lv with 
	| [],[] => Match env_l env
	| p::ps,v::vs => 
		match f envC p v env with
		| Match_type_error _ => Match_type_error env_l
		| Match _ env' => pmatch_list_helper f envC ps vs env'
		| No_match _ => 
			match pmatch_list_helper f envC ps vs env with
				|Match_type_error _ => Match_type_error env_l
				| _ => No_match env_l
			end
		end
	| _,_ => Match_type_error env_l
	end.

Fixpoint pmatch envC p va (env:env_l) : (match_result (env_l) ):=
	match p,va with
	| Pany,_ => (Match env_l env)
	| Pvar x,_ => Match env_l ((x,va)::env)
	| Plit l,(Litv l') => 
		match l,l' with
		| StrLit l1,StrLit l2 => 
			if (l1 =? l2)%string then
				Match env_l env
			else 
				No_match env_l
		end
	| Pcon (Some n) ps,(Conv (Some stamp') vs) =>
		match nsLookup (nat*stamp) envC n with
		| Some (l,stamp0) => if andb (same_type stamp' stamp0) (List.length ps =? l) then
								if same_ctor stamp0 stamp' then
									if List.length vs =? l then 
										pmatch_list_helper pmatch envC ps vs env
									else 
										Match_type_error env_l
								else
									No_match env_l
							else
								Match_type_error env_l
		| _ => Match_type_error env_l
		end
	| Pcon None ps,(Conv None vs) =>
		if List.length ps =? List.length vs then
			pmatch_list_helper pmatch envC ps vs env
		else
			Match_type_error env_l
	| Pas p i,_ => pmatch envC p va ((i,va)::env)
	| _,_ => Match_type_error env_l
	end.

Definition pmatch_list := pmatch_list_helper pmatch.

Inductive pmatch_rel envC :pat-> val -> list (varN*val)->list (varN*val)-> Prop :=
| pmatch_any c' env: 
	pmatch_rel envC Pany c' env env
| pmatch_lit l env:
	pmatch_rel envC (Plit (StrLit l)) (Litv (StrLit l)) env env
| pmatch_var x v' env: 
	pmatch_rel envC (Pvar x) v' env ((x,v')::env)
| pmatch_con n l stamp0 stamp' ps vs env env': 
	nsLookup ((nat*stamp)%type) envC n = Some (l,stamp0) ->
	stamp0 = stamp'->
	length ps = l ->
	length vs = l ->
	pmatch_list_rel envC ps vs env env' ->
	pmatch_rel envC (Pcon (Some n) ps) (Conv (Some stamp') vs) env env' 
| pmatch_con_None ps vs env env':
	length ps = length vs ->
	pmatch_list_rel envC ps vs env env' ->
	pmatch_rel envC (Pcon None ps) (Conv None vs) env env'
| pmatch_pas p v i env env' :
	pmatch_rel envC p v ((i,v)::env) env' ->
	pmatch_rel envC (Pas p i) v ((i,v)::env) env'
with pmatch_list_rel envC : (list pat)->(list val)->list (varN*val)->list (varN*val)->Prop := 
|pmatch_nil env: 
	pmatch_list_rel envC [] [] env env
|pmatch_cons p ps v vs env env' env'':
	pmatch_rel envC p v env env' ->
	pmatch_list_rel envC ps vs env' env'' ->
	pmatch_list_rel envC (p::ps) (v::vs) env env''.

Definition is_Match_type_error (m_r : match_result env_l) :=
	match m_r with
	| Match_type_error _ => true
	| _ => false
	end.


Fixpoint can_pmatch_all (envC:env_ctor) (l:list pat) (va:val): bool :=
	match l with
	| [] => true
	| p::ps => 	if (is_Match_type_error (pmatch envC p va [])) then
					false
				else
					can_pmatch_all envC ps va 
	end.

Inductive can_pmatch_all_rel (envC:env_ctor) :list pat->val-> Prop :=  
	| pmatch_all_nil v: can_pmatch_all_rel envC [] v
	| pmatch_all_cons p ps v l: 
		pmatch_rel envC p v [] l ->
		can_pmatch_all_rel envC ps v ->
		can_pmatch_all_rel envC (p::ps) v.


Definition build_rec_env funs cl_env add_to_env :=
	fold_right (fun '(f, x, e) env' => nsBind f ( Recclosure  cl_env funs f) env') add_to_env funs.

Fixpoint find_recfun a b (n:string) (funs:list (string*a*b)) :=
	match funs with 
	| [] => None
	| (f,x,e)::funs' => if (f =? n)%string then
							Some (x,e)
						else 
							find_recfun a b n funs'
	end.

Definition do_opapp (vs : list val) :=
	match vs with
	| [Closure env n e ; v_q] => Some ({| v := nsBind n v_q env.(v val); c := env.(c val)|} , e)
	| [Recclosure env' funs n';v_q] =>
		if ALL_DISTINCT varN (fun x y => (x=?y)%string) (map (fun '(f,_,_)=>f) funs) then
			match find_recfun varN exp n' funs with
			| None => None
			| Some (n,e) => 
				Some ({| v:= nsBind n v_q (build_rec_env funs env' env'.(v val)) ;c:=env'.(c val)|}, e)
			end
		else 
			None
	| _ => None
	end.