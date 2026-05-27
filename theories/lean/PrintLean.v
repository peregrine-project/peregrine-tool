From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import MRString.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import LeanIR.
From Peregrine Require Utils.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  LeanIR → Lean 4 source pretty-printer                             *)
(* ------------------------------------------------------------------ *)

Definition nl : string := String.String "010"%byte String.EmptyString.

Definition concat_with (sep : string) (xs : list string) : string :=
  String.concat sep xs.

(* Use just the last component of a kername.  All emitted definitions
   live inside a single Lean namespace, so collisions only matter
   across modules that happen to share a local name — accepted v1
   limitation. *)
Definition local_name (kn : kername) : string := snd kn.

(* Suffix inductive / constructor names with [_] so we never collide
   with Lean keywords (e.g. [true], [false], [Nat]). *)
Definition ind_name (s : ident) : string := s ++ "_".
Definition ctor_name (s : ident) : string := s ++ "_".

Definition fun_name (kn : kername) : string := local_name kn.

Fixpoint mk_arg_idents (n : nat) : list string :=
  match n with
  | O => []
  | S k => ("a" ++ string_of_nat (n - 1 - k)) :: mk_arg_idents k
  end.
(* mk_arg_idents 3 = ["a0"; "a1"; "a2"]  (reversed-build, restored order) *)

Definition arg_idents (n : nat) : list string :=
  let fix aux (i max : nat) : list string :=
    match i with
    | O => []
    | S k => ("a" ++ string_of_nat (max - i)) :: aux k max
    end in
  aux n n.
(* arg_idents 3 = ["a0"; "a1"; "a2"] *)

(* Format a parameter group: "(x0 x1 .. xn : Obj)" — empty string if no
   parameters. *)
Definition params_group (ids : list string) : string :=
  match ids with
  | [] => ""
  | _ => "(" ++ concat_with " " ids ++ " : Obj)"
  end.

(* ----- Inductive lookup environment ------------------------------- *)

Definition ind_env := list (kername * EAst.mutual_inductive_body).

Definition build_ind_env (decls : list (kername * ldecl)) : ind_env :=
  Utils.filter_map (fun (x : kername * ldecl) =>
    let '(kn, d) := x in
    match d with
    | LInductive mib => Some (kn, mib)
    | _ => None
    end
  ) decls.

Definition lookup_oib (env : ind_env) (ind : inductive) : option EAst.one_inductive_body :=
  match List.find (fun '(kn, _) => eq_kername kn ind.(inductive_mind)) env with
  | Some (_, mib) => nth_error mib.(EAst.ind_bodies) ind.(inductive_ind)
  | None => None
  end.

Definition lookup_ctor_name (env : ind_env) (ind : inductive) (n : nat) : string :=
  match lookup_oib env ind with
  | Some oib =>
    match nth_error oib.(EAst.ind_ctors) n with
    | Some cb => ctor_name (cb.(EAst.cstr_name))
    | None => "MissingCtor_" ++ string_of_nat n
    end
  | None => "MissingInd_" ++ string_of_nat n
  end.

Definition lookup_ind_name (env : ind_env) (ind : inductive) : string :=
  match lookup_oib env ind with
  | Some oib => ind_name (oib.(EAst.ind_name))
  | None => "MissingInd"
  end.

(* ----- Term printer ----------------------------------------------- *)

(* Every recursive call returns a string that names an [Obj]-typed
   Lean expression.  We achieve this by wrapping each emitted term
   in [Peregrine.reflect] (idempotent at runtime).  This eliminates
   the bookkeeping of where conversions are required. *)
Fixpoint print_lterm (env : ind_env) (t : lterm) : string :=
  let reflect s := "(Peregrine.reflect " ++ s ++ ")" in
  match t with
  | LVar id => reflect id
  | LConst kn => reflect (fun_name kn)
  | LCtor ind idx args =>
    let cn := lookup_ctor_name env ind idx in
    let ind_n := lookup_ind_name env ind in
    let body :=
      match args with
      | [] => "(." ++ cn ++ " : " ++ ind_n ++ ")"
      | _ =>
        "((" ++ ind_n ++ "." ++ cn ++ ") "
          ++ concat_with " " (List.map (print_lterm env) args) ++ ")"
      end in
    reflect body
  | LProj p discr =>
    let ind := p.(proj_ind) in
    let arg := p.(proj_arg) in
    let cn := lookup_ctor_name env ind 0 in
    let nargs :=
      match lookup_oib env ind with
      | Some oib =>
        match nth_error oib.(EAst.ind_ctors) 0 with
        | Some cb => cb.(EAst.cstr_nargs)
        | None => 0
        end
      | None => 0
      end in
    let mk_pat (i : nat) :=
      if Nat.eqb i arg then "x" else "_" in
    let pat_args :=
      let fix aux (i : nat) :=
        match i with
        | O => []
        | S k => mk_pat (nargs - i) :: aux k
        end in
      aux nargs in
    reflect ("(match (Peregrine.cast " ++ print_lterm env discr
      ++ " : " ++ lookup_ind_name env ind ++ ") with | ." ++ cn ++ " "
      ++ concat_with " " pat_args ++ " => x)")
  | LApp f x =>
    reflect ("(Peregrine.apply " ++ print_lterm env f
      ++ " " ++ print_lterm env x ++ ")")
  | LLam id body =>
    reflect ("(fun (" ++ id ++ " : Obj) => " ++ print_lterm env body ++ ")")
  | LLet id b body =>
    reflect ("(let " ++ id ++ " : Obj := " ++ print_lterm env b ++ "; "
      ++ print_lterm env body ++ ")")
  | LCase discr ind brs =>
    let ind_n := lookup_ind_name env ind in
    let print_br (i : nat) (br : list ident * lterm) : string :=
      let '(ids, body) := br in
      let cn := lookup_ctor_name env ind i in
      "  | ." ++ cn
        ++ (match ids with [] => "" | _ => " " ++ concat_with " " ids end)
        ++ " => " ++ print_lterm env body in
    let fix print_brs (i : nat) (bs : list (list ident * lterm)) : list string :=
      match bs with
      | [] => []
      | b :: rest => print_br i b :: print_brs (S i) rest
      end in
    reflect ("(match (Peregrine.cast " ++ print_lterm env discr ++ " : "
      ++ ind_n ++ ") with" ++ nl
      ++ concat_with nl (print_brs 0 brs) ++ nl ++ ")")
  | LPanic _ =>
    (* Stand-in Obj for computationally irrelevant terms (tBox
       replacements, unsupported nested tFix).  A well-typed program
       should never inspect such a value at runtime. *)
    reflect "()"
  end.

(* ----- Top-level declaration printer ------------------------------ *)

Definition print_ctor (cb : EAst.constructor_body) : string :=
  let nargs := cb.(EAst.cstr_nargs) in
  let ids := arg_idents nargs in
  "  | " ++ ctor_name (cb.(EAst.cstr_name))
    ++ (match ids with [] => "" | _ => " " ++ params_group ids end).

Definition print_one_inductive (oib : EAst.one_inductive_body) : string :=
  "unsafe inductive " ++ ind_name (oib.(EAst.ind_name)) ++ " where" ++ nl
    ++ concat_with nl (List.map print_ctor (oib.(EAst.ind_ctors))).

Definition print_inductive (mib : EAst.mutual_inductive_body) : string :=
  match mib.(EAst.ind_bodies) with
  | [oib] => print_one_inductive oib
  | bodies =>
    "mutual" ++ nl
      ++ concat_with nl (List.map print_one_inductive bodies) ++ nl
      ++ "end"
  end.

Definition print_lfun (env : ind_env) (name : string) (f : lfun) : string :=
  "unsafe def " ++ name ++ " "
    ++ concat_with " " (List.map (fun id => "(" ++ id ++ " : Obj)") f.(lfun_params))
    ++ " : Obj :=" ++ nl
    ++ "  " ++ print_lterm env f.(lfun_body).

Definition print_decl (env : ind_env) (kn : kername) (d : ldecl) : string :=
  match d with
  | LInductive mib => print_inductive mib
  | LDef f => print_lfun env (fun_name kn) f
  | LRecGroup fs =>
    "mutual" ++ nl
      ++ concat_with nl (List.map (fun '(kn', f) => print_lfun env (fun_name kn') f) fs) ++ nl
      ++ "end"
  end.

Definition preamble (ns : string) : string :=
  "-- Generated by Peregrine" ++ nl
    ++ "import Peregrine.Runtime" ++ nl
    ++ "open Peregrine" ++ nl
    ++ nl
    ++ "namespace " ++ ns ++ nl.

Definition postamble (ns : string) : string :=
  nl ++ "end " ++ ns ++ nl.

Definition print_program (ns : string) (p : lprogram) : string :=
  let env := build_ind_env p.(ldecls) in
  preamble ns
    ++ concat_with (nl ++ nl) (List.map (fun '(kn, d) => print_decl env kn d) p.(ldecls))
    ++ postamble ns.
