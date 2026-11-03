From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst ELiftSubst.
From MetaRocq.Erasure.Typed Require Import ExAst.
From Stdlib Require Import List.

Import ListNotations.
Import MonadNotation.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  Typed lambda-box (ExAst) -> Koka source pretty-printer            *)
(*                                                                    *)
(*  Each inductive becomes a Koka type with type parameters and typed *)
(*  fields, and each constant a function with its type: unlike the    *)
(*  untyped printer ([PrintKoka]) nothing is cast.  Every function    *)
(*  returns [pure], so general recursion and the absurd case          *)
(*  type-check.  Top-level functions take as many arguments as their  *)
(*  body has leading lambdas; a saturated call is a direct call and   *)
(*  any other use builds curried closures, which is the meaning of    *)
(*  the arrow types.  The printer fails, and the untyped backend is   *)
(*  then the way to go, on a type it cannot express ([TAny], a type   *)
(*  variable in head position) and on primitives, projections,        *)
(*  cofixpoints and [lazy].                                           *)
(* ------------------------------------------------------------------ *)

(* Peregrine's [result']: the monad instance of [result] is found through it. *)
Definition kres (T : Type) : Type := result T string.

Definition kt_nl : string := String.String "010"%byte String.EmptyString.

Definition concat_with (sep : string) (xs : list string) : string := String.concat sep xs.

Fixpoint mp_path (mp : modpath) : list ident :=
  match mp with
  | MPfile dp => List.rev dp
  | MPbound dp id _ => List.app (List.rev dp) [id]
  | MPdot mp id => List.app (mp_path mp) [id]
  end.

Definition flat_name (kn : kername) : string :=
  String.concat "_" (List.app (mp_path (fst kn)) [snd kn]).

Definition fun_name (kn : kername) : string := "pg_" ++ flat_name kn.

Definition type_name (kn : kername) : string := "t_" ++ flat_name kn.

Definition var (id : ident) (depth : nat) : string := "v_" ++ id ++ "_" ++ string_of_nat depth.

Definition kty_var (i : nat) : string := "a" ++ string_of_nat i.

Definition nonempty {A} (l : list A) : bool := match l with [] => false | _ => true end.

Section Printer.
  Context (Σ : global_env).
  Context (remap : kername -> option string).

  Definition lookup_mind (kn : kername) : option mutual_inductive_body :=
    match lookup_env Σ kn with
    | Some (InductiveDecl mib) => Some mib
    | _ => None
    end.

  Definition lookup_oib (ind : inductive) : option one_inductive_body :=
    match lookup_mind (inductive_mind ind) with
    | Some mib => nth_error (ind_bodies mib) (inductive_ind ind)
    | None => None
    end.

  Definition ind_type_name (ind : inductive) : kres string :=
    match lookup_oib ind with
    | Some oib => Ok (type_name (fst (inductive_mind ind), ind_name oib))
    | None => Err ("unknown inductive " ++ string_of_kername (inductive_mind ind))
    end.

  (* Constructor names carry their type's name: Koka constructors of different
     types share one namespace. *)
  Definition ctor_name_of (tname : string) (i : nat) (cname : ident) : string :=
    "C_" ++ tname ++ "_" ++ string_of_nat i ++ "_" ++ cname.

  Definition ctor_info (ind : inductive) (i : nat) : kres (string * nat) :=
    match lookup_oib ind with
    | Some oib =>
      match nth_error (ind_ctors oib) i with
      | Some (cname, data, _) =>
        Ok (ctor_name_of (type_name (fst (inductive_mind ind), ind_name oib)) i cname, List.length data)
      | None => Err ("inductive " ++ ind_name oib ++ " has no constructor " ++ string_of_nat i)
      end
    | None => Err ("unknown inductive " ++ string_of_kername (inductive_mind ind))
    end.

  (* ----- Types ----------------------------------------------------- *)

  (* [Γ] names the type variables in scope, by index. *)
  Fixpoint print_type (Γ : list string) (t : box_type) {struct t} : kres string :=
    match t with
    | TBox => Ok "()"
    | TAny => Err "a type that Koka cannot express (TAny)"
    | TArr dom cod =>
      d <- print_type Γ dom;;
      c <- print_type Γ cod;;
      Ok ("((" ++ d ++ ") -> pure " ++ c ++ ")")
    | TApp h a =>
      a' <- print_type Γ a;;
      (fix head (h : box_type) (acc : list string) {struct h} : kres string :=
         match h with
         | TApp h2 a2 => a2' <- print_type Γ a2;; head h2 (a2' :: acc)
         | TInd ind => n <- ind_type_name ind;; Ok (n ++ "<" ++ concat_with ", " acc ++ ">")
         | TConst kn => Ok (type_name kn ++ "<" ++ concat_with ", " acc ++ ">")
         | _ => Err "a type variable applied to arguments"
         end) h [a']
    | TVar n =>
      match nth_error Γ n with
      | Some v => Ok v
      | None => Err ("unbound type variable " ++ string_of_nat n)
      end
    | TInd ind => ind_type_name ind
    | TConst kn => Ok (type_name kn)
    end.

  (* The first [n] argument types of an arrow type, and the result type. *)
  Fixpoint split_arrows (n : nat) (t : box_type) : option (list box_type * box_type) :=
    match n with
    | 0 => Some ([], t)
    | S n' =>
      match t with
      | TArr dom cod =>
        match split_arrows n' cod with
        | Some (doms, r) => Some (dom :: doms, r)
        | None => None
        end
      | _ => None
      end
    end.

  (* ----- Terms ----------------------------------------------------- *)

  (* Arity of every top-level function: its leading lambdas. *)
  Fixpoint lambdas (t : EAst.term) : list name * EAst.term :=
    match t with
    | EAst.tLambda na b => let '(ns, body) := lambdas b in (na :: ns, body)
    | _ => ([], t)
    end.

  (* The body of a constant: a top-level fixpoint is the function itself. *)
  (* The body of a constant: a top-level fixpoint is (a copy of) its member. *)
  Definition const_body (b : EAst.term) : EAst.term :=
    match b with
    | EAst.tFix mfix i =>
      match nth_error mfix i with Some d => EAst.dbody d | None => b end
    | _ => b
    end.

  Definition const_arity (kn : kername) : option nat :=
    match lookup_env Σ kn with
    | Some (ConstantDecl {| cst_body := Some b |}) => Some (List.length (fst (lambdas (const_body b))))
    | _ => None
    end.

  (* Constants without a body that are used must be remapped. *)
  Definition is_thunk (kn : kername) : bool :=
    match lookup_env Σ kn with
    | Some (ConstantDecl {| cst_type := (tvars, _); cst_body := Some b |}) =>
      match lambdas (const_body b) with
      | ([], _) => match tvars with [] => true | _ => false end
      | _ => false
      end
    | _ => false
    end.

  (* A constant whose type is erased denotes [□], which absorbs arguments. *)
  Definition erased_type (kn : kername) : bool :=
    match lookup_env Σ kn with
    | Some (ConstantDecl {| cst_type := (_, TBox) |}) => true
    | _ => false
    end.

  Definition name_ident (na : name) : ident :=
    match na with
    | nAnon => "x"
    | nNamed id => id
    end.

  (* Unary closures around an n-ary call [f] that already has [pre] arguments. *)
  Definition curry (f : string) (pre : list string) (n : nat) : string :=
    let ids := map (fun i => "pg_c" ++ string_of_nat i) (seq 0 n) in
    let call := f ++ "(" ++ concat_with ", " (List.app pre ids) ++ ")" in
    fold_right (fun id acc => "fn(" ++ id ++ ") { " ++ acc ++ " }") call ids.

  Definition apply_unary (h : string) (args : list string) : string :=
    fold_left (fun acc a => "(" ++ acc ++ ")(" ++ a ++ ")") args h.

  (* A head of known arity [n] applied to [args]. *)
  Definition call_known (f : string) (n : nat) (args : list string) : string :=
    if Nat.leb n (List.length args) then
      apply_unary (f ++ "(" ++ concat_with ", " (firstn n args) ++ ")") (skipn n args)
    else curry f args (n - List.length args).

  (* The local context: names of de Bruijn variables, with the arity of the
     functions bound by a fixpoint and the arguments every call to them
     passes first (the parameters a lifted group is closed over). *)
  Definition ctx := list (string * option (nat * list string)).

  (* Accumulator printer: [pending] holds the printed arguments of the
     application spine around [t], leftmost first, so that the head of a spine
     sees all its arguments and a known function gets a direct call.  The
     recursion is structural: lambdas of a fixpoint body are peeled by a
     nested fixpoint on that body. *)
  Fixpoint print_term (Γ : ctx) (t : EAst.term) (pending : list string) {struct t} : kres string :=
    let depth := List.length Γ in
    match t with
    | EAst.tApp f a =>
      a' <- print_term Γ a [];;
      print_term Γ f (a' :: pending)
    (* [□] absorbs its arguments *)
    | EAst.tBox => Ok "()"
    | EAst.tRel n =>
      match nth_error Γ n with
      | Some (v, Some (k, pre)) => Ok (call_known v k (List.app pre pending))
      | Some (v, None) => Ok (apply_unary v pending)
      | None => Err ("unbound variable " ++ string_of_nat n)
      end
    | EAst.tLambda na b =>
      let v := var (name_ident na) depth in
      b' <- print_term ((v, None) :: Γ) b [];;
      Ok (apply_unary ("fn(" ++ v ++ ") { " ++ b' ++ " }") pending)
    | EAst.tLetIn na v b =>
      let x := var (name_ident na) depth in
      v' <- print_term Γ v [];;
      b' <- print_term ((x, None) :: Γ) b [];;
      Ok (apply_unary ("(fn() { val " ++ x ++ " = " ++ v' ++ "; " ++ b' ++ " })()") pending)
    | EAst.tConst kn =>
      match remap kn with
      | Some s => Ok (apply_unary ("(" ++ s ++ ")") pending)
      | None =>
        if andb (erased_type kn) (nonempty pending) then Ok "()" else
        match const_arity kn with
        | Some n =>
          if is_thunk kn then Ok (apply_unary ("pg_force(" ++ fun_name kn ++ ")") pending)
          else if Nat.eqb n 0 then Ok (apply_unary (fun_name kn ++ "()") pending)
          else Ok (call_known (fun_name kn) n pending)
        | None => Err ("constant without a body: " ++ string_of_kername kn)
        end
      end
    | EAst.tConstruct ind i [] =>
      '(cn, n) <- ctor_info ind i;;
      if Nat.eqb n 0 then Ok (apply_unary cn pending) else Ok (call_known cn n pending)
    | EAst.tConstruct _ _ (_ :: _) => Err "constructors as blocks"
    | EAst.tCase (ind, npars) d brs =>
      d' <- print_term Γ d [];;
      match brs with
      | [] => Ok (apply_unary ("(fn() { val pg_d = " ++ d' ++ "; pg_absurd() })()") pending)
      | _ =>
        oib <- match lookup_oib ind with Some o => Ok o | None => Err "unknown inductive in a match" end;;
        let tname := type_name (fst (inductive_mind ind), ind_name oib) in
        let fix print_brs (i : nat) (bs : list (list name * EAst.term)) (cs : list (ident * list (name * box_type) * nat))
          : kres (list string) :=
          match bs, cs with
          | [], [] => Ok []
          | (bctx, body) :: bs', (cname, _, _) :: cs' =>
            let names := List.rev bctx in
            let vars := mapi (fun j na => var (name_ident na) (depth + j)) names in
            let Γ' := List.app (List.rev (map (fun v => (v, None)) vars)) Γ in
            body' <- print_term Γ' body [];;
            rest <- print_brs (S i) bs' cs';;
            let pat := ctor_name_of tname i cname in
            let args := List.app (repeat "_" npars) vars in
            Ok (((match args with [] => pat | _ => pat ++ "(" ++ concat_with ", " args ++ ")" end)
                  ++ " -> " ++ body') :: rest)
          | _, _ => Err "wrong number of branches"
          end in
        brs' <- print_brs 0 brs (ind_ctors oib);;
        Ok (apply_unary ("(match " ++ d' ++ " { " ++ concat_with "; " brs' ++ " })") pending)
      end
    | EAst.tFix mfix idx =>
      (* One fixpoint is a local function.  A nested group of several is
         rejected: Koka's local functions cannot be mutually recursive, and an
         encoding as a recursive local function returning the tuple of the
         members computed wrong results with Koka 3.2.9.  A top-level group is
         lifted to top-level functions ([print_group]). *)
      let single := match mfix with [_] => true | _ => false end in
      let g := "pg_g" ++ string_of_nat depth in
      let ms := mapi (fun j _ => "pg_m" ++ string_of_nat j) mfix in
      let sel j := "(match " ++ g ++ "(()) { (" ++ concat_with ", " ms ++ ") -> pg_m" ++ string_of_nat j ++ " })" in
      let names := if single then mapi (fun j d => var (name_ident (EAst.dname d)) (depth + j)) mfix
                   else mapi (fun j _ => sel j) mfix in
      let arities := map (fun d => List.length (fst (lambdas (EAst.dbody d)))) mfix in
      let Γ' := List.app (List.rev (combine names (map (fun a => Some (a, [])) arities))) Γ in
      let fix peel (u : EAst.term) (Γp : ctx) (pv : list string) {struct u} : kres (list string * string) :=
        match u with
        | EAst.tLambda na b =>
          let v := var (name_ident na) (List.length Γp) in
          peel b ((v, None) :: Γp) (List.app pv [v])
        | _ => body' <- print_term Γp u [];; Ok (pv, body')
        end in
      let fix print_defs (ds : list (EAst.def EAst.term)) (ns : list string) : kres (list string) :=
        match ds, ns with
        | [], _ => Ok []
        | d :: ds', n :: ns' =>
          '(pvars, body') <- peel (EAst.dbody d) Γ' [];;
          match pvars with
          | [] => Err "a fixpoint without parameters"
          | _ =>
            rest <- print_defs ds' ns';;
            Ok ((if single then "fun " ++ n ++ "(" ++ concat_with ", " pvars ++ ") { " ++ body' ++ " }"
                 else "fn(" ++ concat_with ", " pvars ++ ") { " ++ body' ++ " }") :: rest)
          end
        | _, _ => Err "unreachable"
        end in
      defs <- print_defs mfix names;;
      match nth_error names idx, nth_error arities idx with
      | Some n, Some k =>
        if single then Ok ("(fn() { " ++ concat_with "; " defs ++ "; " ++ call_known n k pending ++ " })()")
        else Err "a nested group of mutual fixpoints"
      | _, _ => Err "fixpoint index out of range"
      end
    | EAst.tVar _ => Err "tVar"
    | EAst.tEvar _ _ => Err "tEvar"
    | EAst.tProj _ _ => Err "projections"
    | EAst.tCoFix _ _ => Err "cofixpoints"
    | EAst.tPrim _ => Err "primitive values"
    | EAst.tLazy _ | EAst.tForce _ => Err "lazy and force"
    end.

  (* ----- Declarations ---------------------------------------------- *)

  Definition tvars_of (n : nat) : list string := map kty_var (seq 0 n).

  Fixpoint app_spine (t : EAst.term) (args : list EAst.term) : EAst.term * list EAst.term :=
    match t with
    | EAst.tApp f a => app_spine f (a :: args)
    | _ => (t, args)
    end.

  (* A constant whose body, after its leading lambdas, applies a group of
     mutual fixpoints gets the members as top-level functions
     [pg_<constant>__mJ], which Koka lets call each other; the constant calls
     its member.  The members take the constant's parameters [pre] first when
     their bodies refer to them (lambda lifting: every call passes them
     unchanged).  Koka infers the members' types. *)
  Definition print_group (kn : kername) (pre : list string) (Γp : ctx) (mfix : EAst.mfixpoint EAst.term)
    : kres (list string * ctx) :=
    let names := mapi (fun j _ => fun_name kn ++ "__m" ++ string_of_nat j) mfix in
    let arities := map (fun d => List.length pre + List.length (fst (lambdas (EAst.dbody d)))) mfix in
    let Γg := List.rev (combine names (map (fun a => Some (a, pre)) arities)) in
    let base := List.length Γg + List.length Γp in
    defs <- monad_map (fun '(n, d) =>
        let '(params, inner) := lambdas (EAst.dbody d) in
        let pvars := mapi (fun j na => var (name_ident na) (base + j)) params in
        body' <- print_term (List.app (List.rev (map (fun v => (v, None)) pvars)) (List.app Γg Γp)) inner [];;
        match List.app pre pvars with
        | [] => Err "a fixpoint without parameters"
        | ps => Ok ("fun " ++ n ++ "(" ++ concat_with ", " ps ++ ") { " ++ body' ++ " }")
        end) (combine names mfix);;
    Ok (defs, Γg).

  Definition print_constant (kn : kername) (ty : list name * box_type) (b : EAst.term)
    : kres string :=
    let Γt := tvars_of (List.length (fst ty)) in
    let body := const_body b in
    let '(params, inner) := lambdas body in
    let self := match b with EAst.tFix [_] 0 => [(fun_name kn, Some (List.length params, []))] | _ => [] end in
    match split_arrows (List.length params) (snd ty) with
    | None => Err ("the type of " ++ string_of_kername kn ++ " has fewer arrows than its body has lambdas")
    | Some (doms, res) =>
      doms' <- monad_map (print_type Γt) doms;;
      res' <- print_type Γt res;;
      let base := List.length self in
      let pvars := mapi (fun j na => var (name_ident na) (base + j)) params in
      let Γp := List.app (List.rev (map (fun v => (v, None)) pvars)) self in
      '(pre, body') <-
        match b, app_spine inner [] with
        | EAst.tFix mfix i, _ =>
          (* the constant is its member [i] *)
          if Nat.ltb 1 (List.length mfix) then
            '(defs, Γg) <- print_group kn [] [] mfix;;
            match nth_error (List.rev Γg) i with
            | Some (n, Some (k, _)) => Ok (concat_with kt_nl defs ++ kt_nl, call_known n k pvars)
            | _ => Err "fixpoint index out of range"
            end
          else body' <- print_term Γp inner [];; Ok ("", body')
        | _, (EAst.tFix mfix i, args) =>
          if Nat.ltb 1 (List.length mfix) then
            let closed := forallb (fun d => ELiftSubst.closedn (List.length mfix) (EAst.dbody d)) mfix in
            let lifted := if closed then [] else pvars in
            '(defs, Γg) <- print_group kn lifted Γp mfix;;
            args' <- monad_map (fun a => print_term Γp a []) args;;
            match nth_error (List.rev Γg) i with
            | Some (n, Some (k, pre)) => Ok (concat_with kt_nl defs ++ kt_nl, call_known n k (List.app pre args'))
            | _ => Err "fixpoint index out of range"
            end
          else body' <- print_term Γp inner [];; Ok ("", body')
        | _, _ => body' <- print_term Γp inner [];; Ok ("", body')
        end;;
      match pvars with
      | [] =>
        if is_thunk kn then
          Ok (pre ++ "val " ++ fun_name kn ++ " : delayed<pure," ++ res' ++ "> = delay(fn() { " ++ body' ++ " })")
        else Ok (pre ++ "fun " ++ fun_name kn ++ "() : pure " ++ res' ++ " { " ++ body' ++ " }")
      | _ =>
        Ok (pre ++ "fun " ++ fun_name kn ++ "(" ++
            concat_with ", " (map (fun '(v, t) => v ++ " : " ++ t) (combine pvars doms')) ++
            ") : pure " ++ res' ++ " { " ++ body' ++ " }")
      end
    end.

  Definition print_inductive (kn : kername) (mib : mutual_inductive_body) : kres string :=
    decls <- monad_map (fun oib =>
      let Γt := tvars_of (List.length (ind_type_vars oib)) in
      let tname := type_name (fst kn, ind_name oib) in
      ctors <- monad_map (fun '(i, (cname, data, _)) =>
          fields <- monad_map (fun '(j, (_, bt)) => t <- print_type Γt bt;; Ok ("f" ++ string_of_nat j ++ " : " ++ t))
                              (combine (seq 0 (List.length data)) data);;
          let cn := ctor_name_of tname i cname in
          Ok (match fields with [] => cn | _ => cn ++ "( " ++ concat_with ", " fields ++ " )" end))
        (combine (seq 0 (List.length (ind_ctors oib))) (ind_ctors oib));;
      let params := match Γt with [] => "" | _ => "<" ++ concat_with ", " Γt ++ ">" end in
      Ok ("type " ++ tname ++ params ++ " { " ++ concat_with "; " ctors ++ " }"))
      (ind_bodies mib);;
    Ok (concat_with kt_nl decls).

  Definition print_alias (kn : kername) (tvars : list type_var_info) (bt : box_type) : kres string :=
    let Γt := tvars_of (List.length tvars) in
    t <- print_type Γt bt;;
    let params := match Γt with [] => "" | _ => "<" ++ concat_with ", " Γt ++ ">" end in
    Ok ("alias " ++ type_name kn ++ params ++ " = " ++ t).

  Definition print_decl (d : kername * bool * global_decl) : kres (option string) :=
    let '(kn, has_deps, decl) := d in
    if negb has_deps then Ok None else
    match decl with
    | ConstantDecl {| cst_type := ty; cst_body := Some b |} =>
      match remap kn with
      | Some _ => Ok None
      | None => s <- print_constant kn ty b;; Ok (Some s)
      end
    | ConstantDecl {| cst_body := None |} => Ok None
    | InductiveDecl mib => s <- print_inductive kn mib;; Ok (Some s)
    | TypeAliasDecl (Some (tvars, bt)) => s <- print_alias kn tvars bt;; Ok (Some s)
    | TypeAliasDecl None => Ok None
    end.

End Printer.

Definition preamble (module : string) : string :=
  (match module with "" => "" | _ => "module " ++ module ++ kt_nl end)
    ++ "// Generated by Peregrine (typed Koka backend)." ++ kt_nl
    ++ "import std/core/unsafe" ++ kt_nl
    ++ "fun pg_force( d : delayed<pure,a> ) : pure a { unsafe-total(fn() { force(d) }) }" ++ kt_nl
    ++ "fun pg_absurd() : pure a { throw(""peregrine: absurd case"") }" ++ kt_nl.

Definition print_program (remap : kername -> option string) (module : string) (Σ : global_env)
  : kres string :=
  decls <- monad_map (print_decl Σ remap) (List.rev Σ);;
  let present := fold_right (fun o acc => match o with Some s => s :: acc | None => acc end) [] decls in
  Ok (preamble module ++ kt_nl ++ concat_with kt_nl present ++ kt_nl).
