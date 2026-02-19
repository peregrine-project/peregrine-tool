From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia List Peano Nat Bool.
Import ListNotations.


Fixpoint ALOOKUP b (v:list (string*b)) (n:string) :=
	match v with
	| [] => None
	| (m,k)::q => if (m =? n)%string then Some k else ALOOKUP b q n
	end. 


Inductive RTC a (rel :(a->a->Prop)) : (a->a->Prop) := 
	| reflexivity: forall x, RTC a rel x x
	| transitivity: forall x y z, rel x y -> RTC a rel y z -> RTC a rel x z. (*one step then the rest of the way*)

Inductive NOT_MEM_rel a : a-> list a-> Prop:=
	|not_mem_nil e : NOT_MEM_rel a e []
	|not_mem_cons e h t : 
		h <> e ->
		NOT_MEM_rel a e t ->
		NOT_MEM_rel a e (h::t).

Inductive ALL_DISTINCT_rel a : list a -> Prop :=
| distinct_nil : ALL_DISTINCT_rel a []
| distinct_cons e t : 
	NOT_MEM_rel a e t ->
	ALL_DISTINCT_rel a t ->
	ALL_DISTINCT_rel a (e::t).

Fixpoint NOT_MEM a eq (e:a) (l:list a):bool:=
	match l with
	| [] => true
	| h::q => andb (eq h e) (NOT_MEM a eq e q)
	end.

Fixpoint ALL_DISTINCT a (eq:a->a->bool) (l:list a):bool :=
	match l with
	| [] => true 
	| e::es => andb (NOT_MEM a eq e es) (ALL_DISTINCT a eq es)
	end.