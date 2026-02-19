From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia List Peano Nat.
From Equations Require Import Equations.
From CakeML Require Import functions.
Import ListNotations.



Notation varN := string (only parsing).
Notation modN := string (only parsing).
Notation conN := string (only parsing).


Inductive id :=
| Short (n:varN) 
| Long (m:modN) (nm:id). (*mn : module name*)

Inductive op_class := (*operator class to group behavior*)
	|FunApp.

Inductive op :=  (*all possible operations*)
	|Opapp.

Inductive opClass : op -> op_class ->Prop:=
	|FunClass: opClass Opapp FunApp.

Definition getOpClass (o:op) :=
match o with
|Opapp => FunApp
end.

Inductive lit :=
| StrLit (s:string).

Inductive pat :=
| Pany (* _ *)
| Plit (l:lit)
| Pvar (v:varN)
| Pcon (n:option id) (p:list pat)
| Pas (p : pat) (n:varN).

Inductive exp :=
| Lit (l:lit)
| Raise (e:exp)
| Handle (e:exp) (p: list(pat*exp))
| Con (n : option id) (es:list exp)
| Var (n : id)
| App (op : op) (es : list exp)
| Fun (n : varN) (e : exp)
| Let (n : option varN) (e1:exp) (e2:exp)
| Mat (m:exp) ( p : list (pat*exp))
| Letrec (f:list (varN*varN*exp)) (e:exp).


Fixpoint pat_bindings_list_helper (f:pat->list varN->list varN) (l:list pat) (already_bound:list varN):list varN :=
match l with 
| [] => already_bound
| p::ps => pat_bindings_list_helper f ps (f p already_bound)
end.

Fixpoint pat_bindings (p:pat) (already_bound:list varN):list varN:= 
match p with
| Pany |Plit _  => already_bound
| Pvar n => (n::already_bound)
| Pcon v0 ps => pat_bindings_list_helper pat_bindings ps already_bound
| Pas p' i =>  pat_bindings p' (i::already_bound)
end.

Definition pat_bindings_list := pat_bindings_list_helper pat_bindings.