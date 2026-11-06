From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst ELiftSubst EAstUtils.
From Peregrine Require Import EBorrow.
From MetaRocq.Erasure.Typed Require Import ExAst.
From Stdlib Require Import List.
From Stdlib.Strings Require Byte.

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

(* Koka treats [x_Sigma] and [x_sigma] as one name, and sha256.v defines both
   [Sigma_1] and [sigma_1].  A name with a leading capital gets a prefix. *)
Definition uncapitalised (s : ident) : ident :=
  match s with
  | String.String c _ =>
    let n := Byte.to_nat c in
    if andb (Nat.leb 65 n) (Nat.leb n 90) then "u" ++ s else s
  | _ => s
  end.

Definition flat_name (kn : kername) : string :=
  String.concat "_" (List.app (mp_path (fst kn)) [uncapitalised (snd kn)]).

Definition fun_name (kn : kername) : string := "pg_" ++ flat_name kn.

Definition type_name (kn : kername) : string := "t_" ++ flat_name kn.

Definition var (id : ident) (depth : nat) : string := "v_" ++ id ++ "_" ++ string_of_nat depth.

Definition kty_var (i : nat) : string := "a" ++ string_of_nat i.

Definition nonempty {A} (l : list A) : bool := match l with [] => false | _ => true end.

Section Printer.
  Context (Σ : global_env).
  (* A remapped constant: the Koka expression and its arity.  An inductive whose
     name is remapped is a natural number on Koka's [int] ([is_native]). *)
  Context (remap : kername -> option (string * nat)).
  (* Borrowed parameters ([EBorrow]), printed [^x]. *)
  Context (bms : modes).

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

  Definition is_native (ind : inductive) : bool :=
    match remap (inductive_mind ind) with Some _ => true | None => false end.

  Definition ind_type_name (ind : inductive) : kres string :=
    if is_native ind then Ok "int" else
    match lookup_oib ind with
    | Some oib => Ok (type_name (fst (inductive_mind ind), ind_name oib))
    | None => Err ("unknown inductive " ++ string_of_kername (inductive_mind ind))
    end.

  (* Constructor names carry their type's name: Koka constructors of different
     types share one namespace. *)
  Definition ctor_name_of (tname : string) (i : nat) (cname : ident) : string :=
    "C_" ++ tname ++ "_" ++ string_of_nat i ++ "_" ++ cname.

  Definition is_tbox (t : box_type) : bool := match t with TBox => true | _ => false end.

  (* The constructor's name, and per field whether its type is [□]. *)
  Definition ctor_info (ind : inductive) (i : nat) : kres (string * list bool) :=
    match lookup_oib ind with
    | Some oib =>
      match nth_error (ind_ctors oib) i with
      | Some (cname, data, _) =>
        Ok (ctor_name_of (type_name (fst (inductive_mind ind), ind_name oib)) i cname,
            map (fun '(_, t) => is_tbox t) data)
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

  (* [fun x1 .. xk => (fix f ..) x1 .. xk] with a closed fixpoint is the
     fixpoint: the constant is then printed as the top-level function of its
     member, with the member's arity, instead of a function of [k] arguments
     that builds a local function and a closure for the rest. *)
  Definition eta_fix (b : EAst.term) : EAst.term :=
    let '(ps, inner) := lambdas b in
    let k := List.length ps in
    match EAstUtils.decompose_app inner with
    | (EAst.tFix mfix i, args) =>
      if andb (Nat.ltb 0 k) (andb (Nat.eqb (List.length args) k)
           (andb (forallb (fun '(j, a) => match a with EAst.tRel n => Nat.eqb n (k - 1 - j) | _ => false end)
                          (combine (seq 0 k) args))
                 (forallb (fun d => ELiftSubst.closedn (List.length mfix) (EAst.dbody d)) mfix)))
      then EAst.tFix mfix i else b
    | _ => b
    end.

  (* The body of a constant: a top-level fixpoint is (a copy of) its member. *)
  Definition const_body (b0 : EAst.term) : EAst.term :=
    let b := eta_fix b0 in
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

  (* A monomorphic constant without parameters: a [delayed] value. *)
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

  (* A literal of a native natural number: [S (S .. O)] *)
  Fixpoint native_literal (t : EAst.term) : option nat :=
    match t with
    | EAst.tConstruct ind 0 [] => if is_native ind then Some 0 else None
    | EAst.tApp (EAst.tConstruct ind 1 []) a =>
      if is_native ind then option_map S (native_literal a) else None
    | _ => None
    end.

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
      match native_literal t with
      | Some n => Ok (apply_unary (string_of_nat n) pending)
      | None =>
        a' <- print_term Γ a [];;
        print_term Γ f (a' :: pending)
      end
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
      | Some (s, 0) => Ok (apply_unary ("(" ++ s ++ ")") pending)
      | Some (s, n) => Ok (call_known ("(" ++ s ++ ")") n pending)
      | None =>
        if andb (erased_type kn) (nonempty pending) then Ok "()" else
        match const_arity kn with
        | Some n =>
          if is_thunk kn then Ok (apply_unary ("pgk_force(" ++ fun_name kn ++ ")") pending)
          else if Nat.eqb n 0 then Ok (apply_unary (fun_name kn ++ "()") pending)
          else Ok (call_known (fun_name kn) n pending)
        | None => Err ("constant without a body: " ++ string_of_kername kn)
        end
      end
    | EAst.tConstruct ind i [] =>
      if is_native ind then
        match i, pending with
        | 0, _ => Ok (apply_unary "0" pending)
        | _, a :: rest => Ok (apply_unary ("(" ++ a ++ " + 1)") rest)
        | _, [] => Ok "fn(pg_x) { pg_x + 1 }"
        end
      else
      '(cn, boxes) <- ctor_info ind i;;
      (* a field of type [□] gets [()], whatever the argument: type inference
         gives a value parameter of an inductive the type [□] *)
      let fix boxed (bs : list bool) (args : list string) : list string :=
        match bs, args with
        | b :: bs', a :: args' => (if b then "()" else a) :: boxed bs' args'
        | _, _ => args
        end in
      let n := List.length boxes in
      if Nat.eqb n 0 then Ok (apply_unary cn pending) else Ok (call_known cn n (boxed boxes pending))
    | EAst.tConstruct _ _ (_ :: _) => Err "constructors as blocks"
    | EAst.tCase (ind, npars) d brs =>
      d' <- print_term Γ d [];;
      if is_native ind then
        match brs with
        | [(_, b0); ([na], b1)] =>
          let v := var (name_ident na) depth in
          let n := "pg_n" ++ string_of_nat depth in
          b0' <- print_term Γ b0 [];;
          b1' <- print_term ((v, None) :: Γ) b1 [];;
          Ok (apply_unary ("(match " ++ d' ++ " { 0 -> " ++ b0' ++ "; " ++ n ++ " -> { val " ++ v ++ " = " ++ n ++ " - 1; " ++ b1' ++ " } })") pending)
        | _ => Err "a match on a native natural number needs its two branches"
        end
      else
      match brs with
      | [] => Ok (apply_unary ("(fn() { val pg_d = " ++ d' ++ "; pgk_absurd() })()") pending)
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

  (* Parameter [j] of the top-level function [f], [^v] when borrowed. *)
  (* An [int] made by [n - 1] must be dropped after a call that borrows it, so that
     call is no tail call: a parameter of type [int] is not borrowed.  A parameter of
     a local function whose type is not known here is not borrowed either, when
     natural numbers are on [int]. *)
  Definition any_native : bool :=
    existsb (fun '(kn, _, d) =>
               match d with
               | InductiveDecl _ => match remap kn with Some _ => true | None => false end
               | _ => false
               end) Σ.

  Definition param (tys : list (option string)) (f : string) (j : nat) (v : string) : string :=
    let allowed :=
        if any_native
        then match nth_error tys j with
             | Some (Some t) => negb (String.eqb t "int")
             | _ => false
             end
        else true in
    (if andb allowed (borrowed bms f j) then "^" else "") ++ v.

  Definition typed_param (f : string) (j : nat) (v t : string) : string :=
    (if andb (negb (String.eqb t "int")) (borrowed bms f j) then "^" else "") ++ v ++ " : " ++ t.

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
  Definition print_group (kn : kername) (pre : list string) (Γp : ctx) (tys : list (option string)) (mfix : EAst.mfixpoint EAst.term)
    : kres (list string * ctx) :=
    let names := mapi (fun j _ => fun_name kn ++ "__m" ++ string_of_nat j) mfix in
    let arities := map (fun d => List.length pre + List.length (fst (lambdas (EAst.dbody d)))) mfix in
    let Γg := List.rev (combine names (map (fun a => Some (a, pre)) arities)) in
    let base := List.length Γg + List.length Γp in
    defs <- monad_map (fun '(n, d) =>
        let '(params, inner) := lambdas (EAst.dbody d) in
        let pvars := mapi (fun j na => var (name_ident na) (base + j)) params in
        body' <- print_term (List.app (List.rev (map (fun v => (v, None)) pvars)) (List.app Γg Γp)) inner [];;
        match List.app pre (mapi (param tys n) pvars) with
        | [] => Err "a fixpoint without parameters"
        | ps => Ok ("fun " ++ n ++ "(" ++ concat_with ", " ps ++ ") { " ++ body' ++ " }")
        end) (combine names mfix);;
    Ok (defs, Γg).

  (* [TAny] comes from a polymorphic type inside a type, as in the alias
     [ID := forall A, A -> A] of the standard library.  At the top of a constant's type
     its occurrences are one type variable of the constant, as for [id : ID]. *)
  Fixpoint has_any (t : box_type) : bool :=
    match t with
    | TAny => true
    | TArr a b | TApp a b => orb (has_any a) (has_any b)
    | _ => false
    end.

  Fixpoint any_to_var (n : nat) (t : box_type) : box_type :=
    match t with
    | TAny => TVar n
    | TArr a b => TArr (any_to_var n a) (any_to_var n b)
    | TApp a b => TApp (any_to_var n a) (any_to_var n b)
    | _ => t
    end.

  Definition is_any_alias (kn : kername) : bool :=
    match lookup_env Σ kn with
    | Some (TypeAliasDecl (Some ([], bt))) => has_any bt
    | _ => false
    end.

  Definition expand_any_alias (ty : list name * box_type) : list name * box_type :=
    match snd ty with
    | TConst kn =>
      match lookup_env Σ kn with
      | Some (TypeAliasDecl (Some ([], bt))) =>
        if has_any bt then (List.app (fst ty) [BasicAst.nAnon], any_to_var (List.length (fst ty)) bt) else ty
      | _ => ty
      end
    | _ => ty
    end.

  Definition print_constant (kn : kername) (ty : list name * box_type) (b0 : EAst.term)
    : kres string :=
    let b := eta_fix b0 in
    let ty := expand_any_alias ty in
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
            '(defs, Γg) <- print_group kn [] [] [] mfix;;
            match nth_error (List.rev Γg) i with
            | Some (n, Some (k, _)) => Ok (concat_with kt_nl defs ++ kt_nl, call_known n k pvars)
            | _ => Err "fixpoint index out of range"
            end
          else body' <- print_term Γp inner [];; Ok ("", body')
        | _, (EAst.tFix mfix i, args) =>
          (* also for a single fixpoint: Koka honours [^] only on top-level functions *)
          let closed := forallb (fun d => ELiftSubst.closedn (List.length mfix) (EAst.dbody d)) mfix in
          let lifted := if closed then [] else pvars in
          (* a single fixpoint takes the types of its arguments, then the remaining arrows *)
          let arg_tys := map (fun a => match a with
                                       | EAst.tRel m =>
                                         if Nat.ltb m (List.length pvars)
                                         then nth_error doms' (List.length pvars - 1 - m)
                                         else None
                                       | _ => None
                                       end) args in
          let fix arrows t := match t with TArr a b => a :: arrows b | _ => [] end in
          let rest_tys := map (fun a => match print_type Γt a with Ok s => Some s | Err _ => None end)
                              (arrows res) in
          let tys := if Nat.eqb (List.length mfix) 1 then List.app arg_tys rest_tys else [] in
          '(defs, Γg) <- print_group kn lifted Γp tys mfix;;
          args' <- monad_map (fun a => print_term Γp a []) args;;
          match nth_error (List.rev Γg) i with
          | Some (n, Some (k, pre)) => Ok (concat_with kt_nl defs ++ kt_nl, call_known n k (List.app pre args'))
          | _ => Err "fixpoint index out of range"
          end
        | _, _ => body' <- print_term Γp inner [];; Ok ("", body')
        end;;
      match pvars with
      | [] =>
        if is_thunk kn then
          Ok (pre ++ "val " ++ fun_name kn ++ " : delayed<pure," ++ res' ++ "> = delay(fn() { " ++ body' ++ " })")
        else Ok (pre ++ "fun " ++ fun_name kn ++ "() : pure " ++ res' ++ " { " ++ body' ++ " }")
      | _ =>
        Ok (pre ++ "fun " ++ fun_name kn ++ "(" ++
            concat_with ", " (mapi (fun j '(v, t) => typed_param (fun_name kn) j v t) (combine pvars doms')) ++
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
    | TypeAliasDecl (Some (tvars, bt)) =>
      if is_any_alias kn then Ok None else s <- print_alias kn tvars bt;; Ok (Some s)
    | TypeAliasDecl None => Ok None
    end.

  (* ----- The functions, for borrow inference ----------------------- *)

  (* A constant called as a known function of its arity. *)
  Definition const_fn (kn : kername) : option (fid * nat) :=
    match remap kn with
    | Some _ => None
    | None =>
      if is_thunk kn then None else
      match const_arity kn with
      | Some (S _ as n) => Some (fun_name kn, n)
      | _ => None
      end
    end.

  Definition group_fns (kn : kername) (outer : nat) (mfix : EAst.mfixpoint EAst.term) : list fn_def :=
    let names := mapi (fun j _ => fun_name kn ++ "__m" ++ string_of_nat j) mfix in
    let ars := map (fun d => List.length (fst (lambdas (EAst.dbody d)))) mfix in
    let funs := List.rev (map (fun '(n, a) => VFun n a) (combine names ars)) in
    map (fun '(n, d) =>
      let '(ps, inner) := lambdas (EAst.dbody d) in
      {| fd_id := n; fd_arity := List.length ps; fd_body := inner;
         fd_ctx := List.app funs (repeat VOther outer); fd_group := names |})
      (combine names mfix).

  (* The top-level functions [print_constant] prints for a constant. *)
  Definition const_fns (kn : kername) (b0 : EAst.term) : list fn_def :=
    let b := eta_fix b0 in
    let '(params, inner) := lambdas (const_body b) in
    let n := List.length params in
    let me := fun_name kn in
    let calls (f : string) := EAst.mkApps (EAst.tRel n) (map EAst.tRel (List.rev (seq 0 n))) in
    match n with
    | 0 => []
    | _ =>
      match b with
      | EAst.tFix [_] 0 =>
        [{| fd_id := me; fd_arity := n; fd_body := inner; fd_ctx := [VFun me n]; fd_group := [me] |}]
      | EAst.tFix mfix i =>
        let gs := group_fns kn 0 mfix in
        let mi := fun_name kn ++ "__m" ++ string_of_nat i in
        {| fd_id := me; fd_arity := n; fd_body := calls mi; fd_ctx := [VFun mi n]; fd_group := [me] |} :: gs
      | _ =>
        let gs := match EAstUtils.decompose_app inner with
                  | (EAst.tFix mfix _, _) => group_fns kn n mfix
                  | _ => []
                  end in
        {| fd_id := me; fd_arity := n; fd_body := inner; fd_ctx := []; fd_group := [me] |} :: gs
      end
    end.

  Definition fn_table : list fn_def :=
    List.concat (map (fun '(kn, _, decl) =>
      match decl with
      | ConstantDecl {| cst_body := Some b |} =>
        match remap kn with Some _ => [] | None => const_fns kn b end
      | _ => []
      end) Σ).

End Printer.

(* Koka reuses a matched cell for a constructor of the same size: a branch
   binding [k > 0] fields that applies a constructor to [k] arguments. *)
Fixpoint allocates (k : nat) (t : EAst.term) {struct t} : bool :=
  match t with
  | EAst.tApp f a =>
    orb (match EAstUtils.decompose_app t with
         | (EAst.tConstruct _ _ [], args) => Nat.eqb (List.length args) k
         | _ => false
         end) (orb (allocates k f) (allocates k a))
  | EAst.tLambda _ b => allocates k b
  | EAst.tLetIn _ v b => orb (allocates k v) (allocates k b)
  | EAst.tCase _ d brs => orb (allocates k d) (existsb (fun br => allocates k (snd br)) brs)
  | EAst.tFix mfix _ => existsb (fun d => allocates k (EAst.dbody d)) mfix
  | _ => false
  end.

Definition koka_reuse (k : nat) (b : EAst.term) : bool := andb (Nat.ltb 0 k) (allocates k b).

(* The helpers are named [pgk_..]: every generated name starts with [pg_], [t_],
   [v_] or [C_], so none can clash with them. *)
Definition preamble (imports : list string) (module : string) : string :=
  (match module with "" => "" | _ => "module " ++ module ++ kt_nl end)
    ++ "// Generated by Peregrine (typed Koka backend)." ++ kt_nl
    ++ "import std/core/unsafe" ++ kt_nl
    ++ String.concat "" (List.map (fun m => "import " ++ m ++ kt_nl) imports)
    ++ "fun pgk_force( d : delayed<pure,a> ) : pure a { unsafe-total(fn() { force(d) }) }" ++ kt_nl
    ++ "fun pgk_absurd() : pure a { throw(""peregrine: absurd case"") }" ++ kt_nl.

(* Koka compares identifiers case-insensitively: [pg_x_fooBar] and [pg_x_foobar], or
   [t_m_Tree] and [t_m_tree], are one name to it.  Such a program is rejected with
   both names. *)
Definition lower_byte (c : Byte.byte) : Byte.byte :=
  let n := Byte.to_nat c in
  if andb (Nat.leb 65 n) (Nat.leb n 90)
  then match Byte.of_nat (n + 32) with Some b => b | None => c end
  else c.

Fixpoint lower_string (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String c r => String.String (lower_byte c) (lower_string r)
  end.

Definition decl_names (Σ : global_env) : list string :=
  flat_map (fun '(kn, has_deps, decl) =>
    if negb has_deps then [] else
    match decl with
    | ConstantDecl _ => [fun_name kn]
    | InductiveDecl mib => map (fun oib => type_name (fst kn, ind_name oib)) (ind_bodies mib)
    | TypeAliasDecl _ => [type_name kn]
    end) Σ.

Fixpoint first_clash (seen : list (string * string)) (names : list string) : option (string * string) :=
  match names with
  | [] => None
  | n :: ns =>
    let l := lower_string n in
    match List.find (fun '(l', _) => String.eqb l l') seen with
    | Some (_, n') => if String.eqb n n' then first_clash seen ns else Some (n', n)
    | None => first_clash ((l, n) :: seen) ns
    end
  end.

Definition print_program (remap : kername -> option (string * nat)) (imports : list string)
  (module : string) (Σ : global_env) : kres string :=
  match first_clash [] (decl_names Σ) with
  | Some (a, b) => Err ("names that differ only in case, which Koka identifies: " ++ a ++ " and " ++ b)
  | None =>
    let fns := fn_table Σ remap in
    let bms := borrow_modes (const_fn Σ remap) koka_reuse fns in
    decls <- monad_map (print_decl Σ remap bms) (List.rev Σ);;
    let present := fold_right (fun o acc => match o with Some s => s :: acc | None => acc end) [] decls in
    Ok (preamble imports module ++ kt_nl ++ concat_with kt_nl present ++ kt_nl)
  end.
