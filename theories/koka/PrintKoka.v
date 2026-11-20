From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import MRString.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import LeanIR.
From Peregrine Require Import PrintPrim.
(* The Koka backend shares the Lean backend's IR ([LeanIR]), compiler
   ([LeanCompile]) and the name-disambiguation and inductive-lookup
   helpers of its printer; only the Koka syntax below is specific. *)
From Peregrine Require Import PrintLean(nl, concat_with, full_name, base_name,
  ind_env, build_ind_env, lookup_oib, dup_base_names, dup_ind_names, pick_ind_name).
From Peregrine Require Import PrintFSharp(fs_module_name).
From Peregrine Require Utils.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  LeanIR → Koka source pretty-printer                               *)
(*                                                                    *)
(*  Every emitted expression has static type [any].  [pg_cast] is an  *)
(*  identity [extern] that converts between [any] and a concrete type:*)
(*  constructors are cast to [any] after construction, discriminants  *)
(*  are cast to their datatype before a [match], and function values  *)
(*  are cast to [(any) -> pure any] before an application.  Every     *)
(*  function returns [pure any], so general recursion ([div]) and an  *)
(*  incomplete projection ([exn]) are allowed.  Saturated calls to    *)
(*  known n-ary definitions are direct calls; under-applied heads are *)
(*  wrapped in unary closures ([curry_wrapper]).  The output uses     *)
(*  braces and semicolons only, so layout never matters.              *)
(* ------------------------------------------------------------------ *)

(* Koka identifiers: functions and values start with a lower-case letter,
   types too, constructors with an upper-case letter.  A fixed prefix gives
   every class its case and keeps every name apart from Koka's keywords and
   from the prelude below ([pg_cast], [pg_apply], ...): function names start
   with [pg_] followed by an upper-case or digit-free part chosen by
   [full_name], locals with [v_], types with [t_] and constructors with [C_]. *)
Definition fun_name (dups : list string) (full : bool) (default_module : string) (kn : kername) : string :=
  "pg_" ++ (if full then full_name dups default_module kn else base_name kn).

Definition var (id : ident) : string := "v_" ++ id.

Definition type_name (ind_dups : list string) (mp : modpath) (s : ident) : string :=
  "t_" ++ pick_ind_name ind_dups mp s.

Definition lookup_type_name (ind_dups : list string) (env : ind_env) (ind : inductive) : string :=
  match lookup_oib env ind with
  | Some oib => type_name ind_dups (fst ind.(inductive_mind)) oib.(EAst.ind_name)
  | None => "t_missing_" ++ string_of_nat ind.(inductive_ind)
  end.

(* Constructor names carry their type's name, because Koka constructors of
   different types share one namespace.  The constructor index makes two
   source names that differ only in case distinct. *)
Definition ctor_names (tname : string) (oib : EAst.one_inductive_body) : list string :=
  let fix go (i : nat) (cs : list EAst.constructor_body) : list string :=
    match cs with
    | [] => []
    | cb :: rest => ("C_" ++ tname ++ "_" ++ string_of_nat i ++ "_" ++ cb.(EAst.cstr_name)) :: go (S i) rest
    end in
  go 0 oib.(EAst.ind_ctors).

Definition lookup_ctor_name (ind_dups : list string) (env : ind_env) (ind : inductive) (n : nat) : string :=
  match lookup_oib env ind with
  | Some oib =>
    let tname := type_name ind_dups (fst ind.(inductive_mind)) oib.(EAst.ind_name) in
    match nth_error (ctor_names tname oib) n with
    | Some s => s
    | None => "C_missing_" ++ string_of_nat n
    end
  | None => "C_missing_" ++ string_of_nat n
  end.

Definition ctor_nargs (env : ind_env) (ind : inductive) (n : nat) : nat :=
  match lookup_oib env ind with
  | Some oib =>
    match nth_error oib.(EAst.ind_ctors) n with
    | Some cb => cb.(EAst.cstr_nargs)
    | None => 0
    end
  | None => 0
  end.

(* [f0 : any, f1 : any, ...] — the fields of a constructor. *)
Definition fields (n : nat) : string :=
  let fix go (i : nat) (k : nat) : list string :=
    match k with
    | O => []
    | S k' => ("f" ++ string_of_nat i ++ " : any") :: go (S i) k'
    end in
  concat_with ", " (go 0 n).

Definition params (ids : list ident) : string :=
  concat_with ", " (List.map (fun id => var id ++ " : any") ids).

(* ----- Inductive declarations -------------------------------------- *)

(* One Koka type per body of a mutual block.  Fields have type [any], so
   the types never refer to each other.  Koka accepts a type with no
   constructors. *)
Definition print_one_inductive (ind_dups : list string) (mp : modpath)
                               (oib : EAst.one_inductive_body) : string :=
  let tname := type_name ind_dups mp oib.(EAst.ind_name) in
  let ctors := List.combine (ctor_names tname oib) oib.(EAst.ind_ctors) in
  "type " ++ tname ++ " { "
    ++ concat_with "; " (List.map (fun '(cn, cb) =>
         match cb.(EAst.cstr_nargs) with
         | O => cn
         | n => cn ++ "( " ++ fields n ++ " )"
         end) ctors)
    ++ " }".

Definition print_inductive (ind_dups : list string) (kn : kername)
                           (mib : EAst.mutual_inductive_body) : string :=
  concat_with nl (List.map (print_one_inductive ind_dups (fst kn)) mib.(EAst.ind_bodies)).

(* ----- Arity bookkeeping (as in the F# printer) -------------------- *)

Definition fun_arities (decls : list (kername * ldecl)) : list (kername * nat) :=
  List.concat (List.map (fun (x : kername * ldecl) =>
    let '(kn, d) := x in
    match d with
    | LDef f => [(kn, List.length f.(lfun_params))]
    | LRecGroup fs => List.map (fun '(kn', f) => (kn', List.length f.(lfun_params))) fs
    | LInductive _ => []
    end) decls).

Definition lookup_local (id : ident) (locals : list (ident * nat)) : option nat :=
  match List.find (fun '(id', _) => String.eqb id' id) locals with
  | Some (_, n) => Some n
  | None => None
  end.

Definition remove_locals (ids : list ident) (locals : list (ident * nat)) : list (ident * nat) :=
  List.filter (fun '(id, _) => negb (List.existsb (String.eqb id) ids)) locals.

Fixpoint peel_lams (t : lterm) : list ident * lterm :=
  match t with
  | LLam id b => let '(ids, body) := peel_lams b in (id :: ids, body)
  | _ => ([], t)
  end.

(* ----- Call shapes ------------------------------------------------- *)

Definition wrap_applies (s : string) (args : list string) : string :=
  List.fold_left (fun acc a => "pg_apply(" ++ acc ++ ", " ++ a ++ ")") args s.

(* An n-ary function as an [any]: a chain of unary closures.  The wrapper
   variables [pg_c0 ...] cannot collide with locals, which start with [v_]. *)
Definition curry_wrapper (name : string) (n : nat) : string :=
  match n with
  | O => name
  | S O => "pg_cast(" ++ name ++ ")"
  | _ =>
    let ids :=
      let fix aux (i max : nat) : list string :=
        match i with
        | O => []
        | S k => ("pg_c" ++ string_of_nat (max - i)) :: aux k max
        end in
      aux n n in
    let call := name ++ "(" ++ concat_with ", " ids ++ ")" in
    let fix wrap (rest : list string) : string :=
      match rest with
      | [] => call
      | id :: rest' => "pg_cast(fn(" ++ id ++ " : any) { " ++ wrap rest' ++ " })"
      end in
    wrap ids
  end.

Definition finish_call (name : string) (arity : nat) (pending : list string) : string :=
  match arity with
  | O => wrap_applies name pending
  | _ =>
    if Nat.leb arity (List.length pending) then
      wrap_applies (name ++ "(" ++ concat_with ", " (List.firstn arity pending) ++ ")")
                   (List.skipn arity pending)
    else
      wrap_applies (curry_wrapper name arity) pending
  end.

(* A block in expression position: Koka has no let- or fun-expression,
   so the statements go in an immediately applied closure. *)
Definition block (stmts : list string) (result : string) : string :=
  "(fn() { " ++ concat_with "; " (stmts ++ [result]) ++ " })()".

(* ----- Terms and declarations -------------------------------------- *)

Section Printer.
  Context (dups : list string) (full_names : bool) (default_module : string)
          (env : ind_env) (thunks : list kername) (arities : list (kername * nat))
          (ind_dups : list string).

  Definition is_thunk (kn : kername) : bool :=
    List.existsb (fun k => eq_kername k kn) thunks.

  Definition lookup_arity (kn : kername) : option nat :=
    match List.find (fun '(kn', _) => eq_kername kn' kn) arities with
    | Some (_, n) => Some n
    | None => None
    end.

  Definition scrutinee (d : string) (ind : inductive) : string :=
    "(pg_cast(" ++ d ++ ") : " ++ lookup_type_name ind_dups env ind ++ ")".

  Fixpoint print_kterm_k (locals : list (ident * nat)) (t : lterm) (pending : list string) {struct t} : string :=
    match t with
    | LApp f x =>
      print_kterm_k locals f (print_kterm_k locals x [] :: pending)
    | LVar id =>
      match lookup_local id locals with
      | Some n => finish_call (var id) n pending
      | None => wrap_applies (var id) pending
      end
    | LConst kn =>
      let nm := fun_name dups full_names default_module kn in
      if is_thunk kn then wrap_applies ("pg_force(" ++ nm ++ ")") pending
      else
        match lookup_arity kn with
        | Some n => finish_call nm n pending
        | None => wrap_applies nm pending
        end
    | LCtor ind idx args =>
      let cn := lookup_ctor_name ind_dups env ind idx in
      let fix print_args (ts : list lterm) : list string :=
        match ts with
        | [] => []
        | a :: rest => print_kterm_k locals a [] :: print_args rest
        end in
      let head :=
        match args with
        | [] => "pg_cast(" ++ cn ++ ")"
        | _ => "pg_cast(" ++ cn ++ "(" ++ concat_with ", " (print_args args) ++ "))"
        end in
      wrap_applies head pending
    | LProj p discr =>
      let ind := p.(proj_ind) in
      let nargs := ctor_nargs env ind 0 in
      let pats :=
        let fix aux (i k : nat) : list string :=
          match k with
          | O => []
          | S k' => (if Nat.eqb i p.(proj_arg) then "pg_x" else "_") :: aux (S i) k'
          end in
        aux 0 nargs in
      wrap_applies
        ("(match " ++ scrutinee (print_kterm_k locals discr []) ind ++ " { "
          ++ lookup_ctor_name ind_dups env ind 0 ++ "(" ++ concat_with ", " pats ++ ") -> pg_x })")
        pending
    | LLam id body =>
      wrap_applies
        ("pg_cast(fn(" ++ var id ++ " : any) { "
          ++ print_kterm_k (remove_locals [id] locals) body [] ++ " })")
        pending
    | LLet id b body =>
      wrap_applies
        (block ["val " ++ var id ++ " = " ++ print_kterm_k locals b []]
               (print_kterm_k (remove_locals [id] locals) body []))
        pending
    | LCase discr ind brs =>
      let print_br (i : nat) (br : list ident * lterm) : string :=
        let '(ids, body) := br in
        let cn := lookup_ctor_name ind_dups env ind i in
        let pat :=
          match ids with
          | [] => cn
          | _ => cn ++ "(" ++ concat_with ", " (List.map var ids) ++ ")"
          end in
        pat ++ " -> " ++ print_kterm_k (remove_locals ids locals) body [] in
      let fix print_brs (i : nat) (bs : list (list ident * lterm)) : list string :=
        match bs with
        | [] => []
        | b :: rest => print_br i b :: print_brs (S i) rest
        end in
      match brs with
      | [] =>
        (* A match on an empty type: evaluate the discriminant, then give the
           erased-value placeholder.  Unreachable in a well-typed program. *)
        wrap_applies (block ["val pg_d = " ++ print_kterm_k locals discr []] "pg_boxv") pending
      | _ =>
        wrap_applies
          ("(match " ++ scrutinee (print_kterm_k locals discr []) ind ++ " { "
            ++ concat_with "; " (print_brs 0 brs) ++ " })")
          pending
      end
    | LFix entries idx =>
      (* A nested fixpoint becomes a local function.  As in the F# printer,
         a mutual nested fixpoint and a fixpoint without parameters are not
         produced by any frontend, and fail at run time. *)
      match entries with
      | [(nm, body)] =>
        let ps := fst (peel_lams body) in
        match ps with
        | [] => wrap_applies "throw(""peregrine: value-recursive fix"")" pending
        | _ =>
          let locals' := (nm, List.length ps) :: remove_locals (nm :: ps) locals in
          let fix print_after_lams (u : lterm) : string :=
            match u with
            | LLam _ b => print_after_lams b
            | _ => print_kterm_k locals' u []
            end in
          block ["fun " ++ var nm ++ "( " ++ params ps ++ " ) : pure any { "
                   ++ print_after_lams body ++ " }"]
                (finish_call (var nm) (List.length ps) pending)
        end
      | _ => wrap_applies "throw(""peregrine: mutual nested fix unsupported"")" pending
      end
    | LExtern target args =>
      let args' := List.map (fun a => print_kterm_k locals a []) args in
      let call :=
        match args' with
        | [] => "(" ++ target ++ ")"
        | _ => "(" ++ target ++ ")(" ++ concat_with ", " args' ++ ")"
        end in
      wrap_applies call pending
    | LPrimInt i => wrap_applies ("pg_cast(" ++ prim_int_decimal i ++ ")") pending
    | LPrimString s => wrap_applies ("pg_cast(" ++ prim_string_literal s ++ ")") pending
    | LPanic _ =>
      (* The erased-value placeholder: it absorbs any application. *)
      wrap_applies "pg_boxv" pending
    end.

  (* Nullary constants are memoized [delayed] values, forced on first use,
     which keeps evaluate-once sharing without running them at module
     initialization. *)
  Definition print_kfun (name : string) (f : lfun) : string :=
    match f.(lfun_params) with
    | [] =>
      "val " ++ name ++ " : delayed<pure,any> = delay(fn() { "
        ++ print_kterm_k [] f.(lfun_body) [] ++ " })"
    | ps =>
      "fun " ++ name ++ "( " ++ params ps ++ " ) : pure any { "
        ++ print_kterm_k [] f.(lfun_body) [] ++ " }"
    end.

  (* Koka groups mutually recursive top-level functions by itself. *)
  Definition print_decl (kn : kername) (d : ldecl) : string :=
    match d with
    | LInductive mib => print_inductive ind_dups kn mib
    | LDef f => print_kfun (fun_name dups full_names default_module kn) f
    | LRecGroup fs =>
      concat_with nl (List.map (fun '(kn', f) =>
        print_kfun (fun_name dups full_names default_module kn') f) fs)
    end.

End Printer.

Definition preamble (imports : list string) (module : string) : string :=
  (match module with "" => "" | _ => "module " ++ module ++ nl end)
    ++ "// Generated by Peregrine (Koka backend). Every value has type any." ++ nl
    ++ "import std/core/unsafe" ++ nl
    ++ String.concat "" (List.map (fun m => "import " ++ m ++ nl) imports)
    ++ "extern pg_cast( x : a ) : b { c inline ""#1""; js inline ""#1"" }" ++ nl
    ++ "fun pg_apply( f : any, x : any ) : pure any { (pg_cast(f) : (any) -> pure any)(x) }" ++ nl
    ++ "fun pg_force( d : delayed<pure,any> ) : pure any { unsafe-total(fn() { force(d) }) }" ++ nl
    ++ "// The erased-value placeholder, which absorbs any application." ++ nl
    ++ "fun pg_boxfn( x : any ) : pure any { pg_cast(pg_boxfn) }" ++ nl
    ++ "val pg_boxv : any = pg_cast(pg_boxfn)" ++ nl
    ++ nl.

(* Nullary top-level constants, emitted as [delayed] values. *)
Definition thunk_knames (decls : list (kername * ldecl)) : list kername :=
  List.concat (List.map (fun (x : kername * ldecl) =>
    let '(kn, d) := x in
    match d with
    | LDef f => match f.(lfun_params) with [] => [kn] | _ => [] end
    | LRecGroup fs => Utils.filter_map (fun '(kn', f) =>
        match f.(lfun_params) with [] => Some kn' | _ => None end) fs
    | LInductive _ => []
    end) decls).

Definition print_program (imports : list string) (full_names : bool) (default_module : string)
                         (module : string) (p : lprogram) : string :=
  let default_module := fs_module_name default_module in
  let env := build_ind_env p.(ldecls) in
  let thunks := thunk_knames p.(ldecls) in
  let arities := fun_arities p.(ldecls) in
  let dups := dup_base_names p.(ldecls) in
  let ind_dups := dup_ind_names env in
  preamble imports module
    ++ concat_with nl
         (List.map (fun '(kn, d) =>
            print_decl dups full_names default_module env thunks arities ind_dups kn d) p.(ldecls))
    ++ nl.
