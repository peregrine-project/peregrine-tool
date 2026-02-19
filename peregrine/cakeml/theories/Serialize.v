From MetaRocq.Utils Require Import bytestring ReflectEq utils.
From MetaRocq.Common Require Kernames.

From Stdlib Require Import String Ascii Bool Arith List.
Set Warnings "-masking-absolute-name".
From Ceres Require Import Ceres CeresString CeresFormat CeresSerialize.
Import ListNotations.

From CakeML Require Import ast namespace semanticPrimitives functions bigstep.


Local Open Scope sexp.
Local Open Scope string.



Local Coercion of := String.of_string.

#[export] Instance Serialize_Ident : Serialize varN :=
	fun a => Atom (Str a).

#[export] Instance Serialize_Ident_bs : Serialize bs :=
	fun a => [Atom (Str (String.to_string a))].

#[export] Instance Serialize_id : Serialize id :=
	fun a =>
    match a with
    | Short str => [Atom "Short" ; Atom (Str str)]
    | _ => Atom "notsupported"
    end.

#[local]
Instance Serialize_cakeml_option {A : Type} `{Serialize A} : Serialize (option A) :=
	fun a =>
		match a with
		| None => Atom "NONE"
		| Some n => [Atom "SOME"; to_sexp n]
		end.

#[local]
Instance Serialize_cakeml_list {A : Type} `{serA : Serialize A} : Serialize (list A) :=
	fun a =>
		match a with
		| []%list => Atom "nil"
		| l => @Serialize_list A serA l
		end.

#[local]
Instance Serialize_cakeml_pair {A B : Type} `{Serialize A} `{Serialize B} : Serialize (A * B) :=
	fun '(a,b) =>
		let sexp_a := to_sexp a in
		let sexp_b := to_sexp b in
		match sexp_b with
		| Atom_ x =>
			(* If both are atoms we serialize as expected *)
			[sexp_a; sexp_b]
		| List l =>
			(* If b is a list then CakeML sexp parser expects it to not be nested.
				Only a is allowed to be a nested list *)
			List (sexp_a :: l)
		end.

Fixpoint to_sexp_binding (a : pat) : sexp :=
	match a with
	| Pany => Atom "Pany"
	| Plit (StrLit l) => [Atom "Plit"; Atom "StrLit"; to_sexp l]
	| Pvar v => to_sexp v
	| Pcon n p => [Atom "Pcon"; to_sexp n; (@Serialize_cakeml_list _ to_sexp_binding p)]
	| Pas p n => [Atom "Pas"; to_sexp_binding p; to_sexp n]
	end.

Fixpoint to_sexp_t (a : exp) : sexp :=
	match a with
	| Lit (StrLit l) => [Atom "Lit"; Atom "Strlit"; to_sexp l]
	| Raise e => [Atom "Raise"; to_sexp_t e]
	| Handle e pes =>
		[ Atom "Handle";
			to_sexp_t e;
			@Serialize_cakeml_list _ (@Serialize_cakeml_pair _ _ to_sexp_binding to_sexp_t) pes
		]
  | Con cn es => [Atom "Con"; to_sexp cn; @Serialize_cakeml_list _ to_sexp_t es]
	| Var x => [Atom "Var"; to_sexp x]
	| App op es =>
		[ Atom "App";
			Atom "Opapp";
			@Serialize_cakeml_list _ to_sexp_t es
		]
	| Fun x e => [Atom "Fun"; to_sexp x; to_sexp_t e]
	| Let n e1 e2 => [Atom "Let"; to_sexp n; to_sexp_t e1; to_sexp_t e2]
	| Mat m p => [Atom "Mat"; to_sexp_t m; @Serialize_cakeml_list _ (@Serialize_cakeml_pair _ _ to_sexp_binding to_sexp_t) p]
	| Letrec fs e =>
		[ Atom "Letrec";
			(@Serialize_list _ (fun '(f,x,e') =>
				(@Serialize_cakeml_pair _ _ _ (@Serialize_cakeml_pair _ _ _ to_sexp_t))
				(f, (x, e')))
			fs);
			to_sexp_t e
		]
	end.

#[export] Instance Serialize_t : Serialize exp := to_sexp_t.

Definition global_serializer : Serialize (bytestring.string * option exp) :=
	fun '(i, b) =>
	match b with
	| Some x =>
		[ Atom "Dlet";
	    [Atom "unk"; Atom "unk"];
			to_sexp (String.to_string (i)%bs);
			to_sexp x
		]
	| None =>
		let na := (String.to_string (i)%bs) in
		[ Atom (Raw ("$" ++ na));
			[Atom "global"; Atom (Raw ("$Axioms")); Atom (Raw ("$" ++ na))]
		]
	end.

Definition Serialize_module (names : list bytestring.string) :=
  fun '(m, x) =>
    let name : bs := match m with
							| (x :: l)%list => fst x
							| nil => ""%bs
						end in
    let main := "main"%bs in
		let defs := List.rev ((main, Some x) :: m)%list in
		 @Serialize_list _ global_serializer defs.
