From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia List Peano Nat.
From CakeML Require Import ast.
From CakeML Require Import functions.
Import ListNotations.



Inductive namespace m n v :=
	Bind (var : list (n*v)) (  ns : list (m*namespace m n v) ).

Inductive stamp := 
| TypeStamp (s:string) (n:nat)
| ExnStamp (n:nat).

Record Sem_env a := {
	v: namespace modN varN a;  (*for variables*)
	c: namespace modN conN (nat*(stamp))  (*for constructors*)
}.

Inductive val :=
| Litv (l:lit)
| Closure (env : Sem_env val) (n : varN) (e : exp)
| Conv (n: option stamp) (vs : list val)
| Recclosure (env:Sem_env val) (f:list (varN*varN*exp)) (n:varN).

Inductive error_result :=
	Rraise (v:val).

Inductive result :=
|Rval (va:val)
|Rerr (e:error_result).

Definition alist_to_ns a :=
	Bind modN varN val a []
.

Definition nsBind (n:varN) (x:val) v :=
	match v with
		|Bind _ _ _ var ns => Bind modN varN val ((n,x)::var) ns 
end.

Fixpoint nsLookup c (env :  namespace modN varN c) (n : id):option c :=
	match env,n with
	| Bind _ _ _ v _ ,(Short n) => ALOOKUP c v n
	| Bind _ _ _ _ m , Long mn n =>
		match ALOOKUP ( namespace modN string c) m mn with
		| Some env' => nsLookup c env' n
		| None => None 
	end
end.

Definition nsOptBind (n:option varN) (x:val) env :=
	match n with
	| None => env
	| Some n => nsBind n x env
	end.

Definition nsAppend env1 env2 :=
	match env1,env2 with 
	|Bind _ _ _ v1 m1, Bind _ _ _ v2 m2 => Bind modN varN val (v1++v2) (m1 ++ m2)
end.