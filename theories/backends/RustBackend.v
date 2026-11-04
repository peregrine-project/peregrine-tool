From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require EBorrow.
From MetaRocq.Erasure Require EAst EAstUtils.
From Peregrine Require Import Utils.
From TypedExtraction Require Import PrettyPrinterMonad.
From TypedExtraction Require Import Printing.
From TypedExtraction Require Import RustExtract.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_rust_config := {|
  rust_preamble_top       := "";
  rust_preamble_program   := "";
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
  rust_refcount           := false;
|}.

Definition rust_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
|}.



Definition rust_top_preamble := [
  "#![allow(dead_code)]";
  "#![allow(non_camel_case_types)]";
  "#![allow(unused_imports)]";
  "#![allow(non_snake_case)]";
  "#![allow(unused_variables)]";
  "";
  "use std::marker::PhantomData;";
  "";
  "fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
  "  f";
  "}"
].

Definition rust_program_preamble := [
  "fn alloc<T>(&'a self, t: T) -> &'a T {";
  "  self.__alloc.alloc(t)";
  "}";
  "";
  "fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
  "  self.__alloc.alloc(F)";
  "}"
].

(** The preamble of the reference-counting mode ([rust_refcount]).  Values
    are [Rc<..>] and closures [Rc<dyn Fn(A) -> B + 'a>]; the printer builds a
    value with [__mk], borrows a scrutinee with [__borrow] and applies a closure
    with [__app].  [__own] is for a later precise mode that moves a value out of
    a unique [Rc].  The program has no allocator. *)
Definition rust_rc_top_preamble := [
  "#![allow(dead_code)]";
  "#![allow(non_camel_case_types)]";
  "#![allow(unused_imports)]";
  "#![allow(non_snake_case)]";
  "#![allow(unused_variables)]";
  "";
  "use std::marker::PhantomData;";
  "use std::rc::Rc;";
  "";
  "fn __mk<T>(t: T) -> Rc<T> {";
  "  Rc::new(t)";
  "}";
  "";
  "fn __borrow<T: ?Sized>(x: &Rc<T>) -> &T {";
  "  &**x";
  "}";
  "";
  "fn __own<T: Clone>(x: Rc<T>) -> T {";
  "  Rc::unwrap_or_clone(x)";
  "}";
  "";
  "fn __app<'b, TArg, TRet>(f: Rc<dyn Fn(TArg) -> TRet + 'b>, a: TArg) -> TRet {";
  "  (*f)(a)";
  "}";
  "";
  "// Runs f on a thread with a stack of the given size.  Unary nat recursion,";
  "// and dropping a long Rc chain, recurse once per cell:";
  "// __with_stack(2 << 30, || { let p = Program::new(); ... })";
  "pub fn __with_stack<R: Send>(bytes: usize, f: impl FnOnce() -> R + Send) -> R {";
  "  std::thread::scope(|s| std::thread::Builder::new().stack_size(bytes).spawn_scoped(s, f).unwrap().join().unwrap())";
  "}"
].

Definition rust_rc_program_preamble := [
  "fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> Rc<dyn Fn(TArg) -> TRet + 'a> {";
  "  Rc::new(F)";
  "}";
  "// The numeric remaps keep big numbers behind a reference; with no arena they are leaked";
  "fn alloc<T: 'a>(&'a self, t: T) -> &'a T {";
  "  Box::leak(Box::new(t))";
  "}"
].

Definition mk_preamble (o : rust_config) : Preamble :=
  if o.(rust_refcount) then {|
    top_preamble := rust_rc_top_preamble ++ [o.(rust_preamble_top)];
    program_preamble := rust_rc_program_preamble ++ [o.(rust_preamble_program)];
  |} else {|
    top_preamble := rust_top_preamble ++ [o.(rust_preamble_top)];
    program_preamble := rust_program_preamble ++ [o.(rust_preamble_program)];
  |}.

Definition mk_attributes (attrs : custom_attributes) (o : rust_config) : Kernames.inductive -> string :=
  match attrs with
  | nil => fun _ => o.(rust_default_attributes)
  | _ =>
    fun ind =>
      match List.find (fun '(kn', _) => Kernames.eq_kername ind.(Kernames.inductive_mind) kn') attrs with
      | Some (_, a) => a
      | None => o.(rust_default_attributes)
      end
  end.

Definition mk_remaps (rs : constant_remappings) (is : inductive_remappings) : remaps :=
  let re_inds := filter_map (fun x =>
    match x with
    | StringIndRemap ind r => Some (ind, {|
      re_ind_name  := r.(Config.re_ind_name);
      re_ind_ctors := r.(Config.re_ind_ctors);
      re_ind_match := r.(Config.re_ind_match);
    |})
    | _ => None
    end
  ) is in
  let re_const := filter_map (fun '(kn, r) =>
    if r.(re_const_inl) then None
    else Some (kn, r.(re_const_s))
  ) rs in
  let re_in_const := filter_map (fun '(kn, r) =>
    if r.(re_const_inl) then Some (kn, r.(re_const_s))
    else None
  ) rs in
  {|
  remap_inductive :=
    match re_inds with
    | nil => fun ind => None
    | _ => fun ind =>
      option_map (fun '(_,r) => r)
        (List.find (fun '(ind', _) => Kernames.eq_inductive ind ind') re_inds)
    end;

  remap_constant :=
    match re_const with
    | nil => fun kn => None
    | _ => fun kn =>
      option_map (fun '(_,s) => s)
        (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') re_const)
    end;

  remap_inline_constant :=
    match re_in_const with
    | nil => fun kn => None
    | _ => fun kn =>
      option_map (fun '(_,s) => s)
        (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') re_in_const)
    end;
|}.
(* TODO: support external remapping in Rust backend *)

(* The parameters of the methods the printer prints, as [print_constant] peels
   them: the leading lambdas of [native_rec_body], as far as the type has arrows. *)
Fixpoint peel_params (t : EAst.term) (ty : ExAst.box_type) : nat * EAst.term :=
  match t, ty with
  | EAst.tLambda _ b, ExAst.TArr _ c => let '(n, i) := peel_params b c in (S n, i)
  | _, _ => (0, t)
  end.

Definition rust_fn_table (remaps : remaps) (Σ : ExAst.global_env) : list EBorrow.fn_def :=
  flat_map (fun '(kn, _, d) =>
    match d with
    | ExAst.ConstantDecl {| ExAst.cst_type := (_, ty); ExAst.cst_body := Some b |} =>
      match remap_constant remaps kn, remap_inline_constant remaps kn with
      | None, None =>
        let '(n, i) := peel_params (native_rec_body (fst (ExAst.decompose_arr ty)) kn b) ty in
        match n with
        | 0 => []
        | _ =>
          let id := Kernames.string_of_kername kn in
          [{| EBorrow.fd_id := id; EBorrow.fd_arity := n; EBorrow.fd_body := i;
              EBorrow.fd_ctx := []; EBorrow.fd_group := [id] |}]
        end
      | _, _ => []
      end
    | _ => []
    end) Σ.

Definition rust_const_fn (remaps : remaps) (Σ : ExAst.global_env) (kn : Kernames.kername)
  : option (EBorrow.fid * nat) :=
  match remap_constant remaps kn, remap_inline_constant remaps kn, ExAst.lookup_constant Σ kn with
  | None, None, Some {| ExAst.cst_type := (_, ty); ExAst.cst_body := Some b |} =>
    match fst (peel_params (native_rec_body (fst (ExAst.decompose_arr ty)) kn b) ty) with
    | 0 => None
    | n => Some (Kernames.string_of_kername kn, n)
    end
  | _, _, _ => None
  end.

(* Perceus-style reuse: a branch binding [k > 0] fields that applies a constructor
   to [k] arguments gains from owning the matched cell. *)
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

Definition rc_borrowed_modes (remaps : remaps) (Σ : ExAst.global_env) : Kernames.kername -> nat -> bool :=
  let ms := EBorrow.borrow_modes (rust_const_fn remaps Σ)
              (fun k b => andb (Nat.ltb 0 k) (allocates k b)) (rust_fn_table remaps Σ) in
  fun kn j => EBorrow.borrowed ms (Kernames.string_of_kername kn) j.

Definition mk_config (o : rust_config) (borrowed : Kernames.kername -> nat -> bool) : RustPrintConfig := {|
  term_box_symbol := o.(rust_term_box_symbol);
  type_box_symbol := o.(rust_type_box_symbol);
  any_type_symbol := o.(rust_any_type_symbol);
  print_full_names := o.(rust_print_full_names);
  memory_mode := if o.(rust_refcount) then RcMode else ArenaMode;
  rc_borrowed := borrowed;
|}.



(** The printer prints a remapped constant from its remapping string, which
    takes one parameter per arrow of the constant's type, but it applies the
    constant, at every call site and in its [__curried] wrapper, to as many
    arguments as the constant's body has leading lambdas
    ([RustExtract.get_num_inline_args]).  A fixpoint such as [Nat.add] has
    fewer leading lambdas than arrows, so the two disagree and rustc rejects
    the program.  Give each remapped constant a body of one lambda per arrow;
    the printer never prints the body of a remapped constant. *)
Definition eta_remapped_bodies (remaps : remaps) (Σ : ExAst.global_env) : ExAst.global_env :=
  map (fun '(kn, deps, d) =>
    match d, remap_constant remaps kn with
    | ExAst.ConstantDecl {| ExAst.cst_type := ty; ExAst.cst_body := Some _ |}, Some _ =>
      let n := #|fst (ExAst.decompose_arr (snd ty))| in
      let body := List.fold_right (fun _ t => EAst.tLambda BasicAst.nAnon t) EAst.tBox (repeat tt n) in
      (kn, deps, ExAst.ConstantDecl {| ExAst.cst_type := ty; ExAst.cst_body := Some body |})
    | _, _ => (kn, deps, d)
    end) Σ.

(** Stopgap for benchmarks UPSTREAM_ISSUES entry 3.  Corelib declares
    [id : ID] with [ID := forall A, A -> A].  Typed erasure does not unfold
    the alias, so [id] gets no type parameter and its type erases to the
    arrow-less [ID], printed as [Fn(()) -> Fn(()) -> ()], which rustc rejects
    at uses of [id] at any other type.  In that case only (when types are
    inferred, or once erasure unfolds the alias, [id]'s type has arrows and
    is printed correctly), remap [id] to a generic Rust function; a remap of
    [id] given by the user takes precedence.  The proper fix is in typed
    erasure, which should unfold such an alias before computing the type
    scheme and dearg mask of a constant. *)
Definition id_kn : Kernames.kername := (Kernames.MPfile ["Datatypes"; "Init"; "Corelib"], "id").

Definition id_remap_string (refcount : bool) : string :=
  if refcount then
    "fn ##name##<T: Clone + 'a>(&'a self) -> Rc<dyn Fn(()) -> Rc<dyn Fn(T) -> T + 'a> + 'a> { self.closure(move |_A: ()| self.closure(move |x: T| x)) }"
  else
    "fn ##name##<T: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(T) -> T { self.closure(move |_A: ()| self.closure(move |x: T| x)) }".

Definition id_remap (refcount : bool) : Kernames.kername * remapped_constant :=
  (id_kn, {|
    re_const_ext := None;
    re_const_arity := 0;
    re_const_gc := false;
    re_const_inl := false;
    re_const_s := id_remap_string refcount;
  |}).

Definition default_const_remaps (refcount : bool) (Σ : ExAst.global_env) : constant_remappings :=
  match ExAst.lookup_env Σ id_kn with
  | Some (ExAst.ConstantDecl {| ExAst.cst_type := (_, ty) |}) =>
    match ExAst.decompose_arr ty with
    | ([], _) => [id_remap refcount]
    | _ => []
    end
  | _ => []
  end.

Definition extract_rust (const_remaps : constant_remappings)
                        (ind_remaps : inductive_remappings)
                        (custom_attr : custom_attributes)
                        (opts : rust_config)
                        (file_name : string)
                        (p : ExAst.global_env)
                        : result' (list string) :=
  let remaps := mk_remaps (const_remaps ++ default_const_remaps opts.(rust_refcount) p)%list ind_remaps in
  let attrs := mk_attributes custom_attr opts in
  let preamble := mk_preamble opts in
  let p := eta_remapped_bodies remaps p in
  let config := mk_config opts (if opts.(rust_refcount) then rc_borrowed_modes remaps p
                                else fun _ _ => false) in
  let p := @print_program p remaps config attrs preamble in
  '(_, s) <- finish_print_lines p;;
  Ok s.
