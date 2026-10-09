(** * EHindleyMilner: type inference λ□ → λ□ᵀ, proved to be a section of type
      erasure.  The inferred types themselves are unverified.

    ------------------------------------------------------------------------
    OVERVIEW

    λ□ (untyped extracted terms) and λ□ᵀ (typed extracted terms) share the
    term language [EAst.term]; they differ ONLY in the global environment:

      - λ□  uses [EAst.global_context] = list (kername * EAst.global_decl)
      - λ□ᵀ uses [ExAst.global_env]    = list (kername * bool * ExAst.global_decl)

    where ExAst declarations additionally carry [box_type] annotations.  The
    REVERSE map [ExAst.trans_env : ExAst.global_env -> EAst.global_context]
    forgets those annotations and is used in the verified pipeline
    ([Transforms.trans_env_transform]).

    This module builds the FORWARD map

      infer : EAst.global_context -> result' ExAst.global_env

    an Algorithm-W-style Hindley–Milner inference that DECORATES the untyped
    environment with [box_type]s, or FAILS with a message naming the constant
    and the types that did not unify.  On success the untyped skeleton
    (kernames, bodies, constructor names/arities, projections) is untouched,
    so [infer] is a right inverse (a SECTION) of [trans_env]:

      infer Σ = Ok Σ' -> trans_env Σ' = Σ.              (* [infer_section] *)

    ------------------------------------------------------------------------
    VERIFICATION STATUS

    - PROVED (Qed, no admits, no added axioms):
        [infer_section : forall Σ Σ', infer Σ = Ok Σ' -> trans_env Σ' = Σ].
      This holds *by construction*: the emitted environment is [map
      (emit_decl T E) Σ], and [emit_decl] only fills in the type fields that
      [trans_env] discards.  The proof does not inspect the inferred types.
      [infer_kernames] and [infer_has_deps] are the corresponding structural
      facts.  [EHindleyMilnerSound.v] proves that the emitted annotations are
      well scoped: every type variable of a constant scheme is bound by its
      quantifier list, and every type variable in a constructor field or
      projection is below the number of [ind_type_vars].  [Print Assumptions]
      at the bottom of both files reports only the primitive types
      [PrimString.string], [PrimInt63.int], [PrimFloat.float] mentioned by
      [EAst.term].

    - NOT PROVED: that the [box_type]s describe the terms (soundness w.r.t. a
      typing judgement for λ□ᵀ, which does not exist yet), principality, or
      completeness.  The datatype signatures are reconstructed from USES
      (see below) by a deterministic heuristic that has no principal
      solution in general; it can produce a declaration more polymorphic
      than the source one, or fail on programs the source type checker
      accepts.  Failure is always reported: nothing is ever emitted with a
      fallback type.

    ------------------------------------------------------------------------
    INFERENCE ALGORITHM

    1. UNIFICATION is an idempotent substitution-map solver with occurs-check.
       [extend] fully zonks the right-hand side against the current (idempotent)
       substitution, runs the occurs-check, and applies the new binding to the
       codomains of all existing bindings.  This maintains the invariant that
       the substitution is IDEMPOTENT, so a single structural [zonk] pass is a
       FULL zonk (all chains resolved).  [TBox] and [TAny] unify only with
       themselves; [TInd]/[TConst] by name.  [unify] is fuel-bounded for
       structural termination; running out of fuel is a failure.

    2. CROSS-CONSTANT SCHEME PROPAGATION.  Constants are processed in dependency
       (topological) order — [infer_go] recurses on the tail FIRST, and an
       extracted environment lists a declaration before its dependencies, so the
       tail already holds every dependency's scheme.  Each constant's inferred
       type is Damas–Milner GENERALIZED ([generalize]) and recorded in a scheme
       table; at every [tConst] use-site the scheme is INSTANTIATED with fresh
       variables ([instantiate]).  A constant absent from the table (used before
       its declaration) is an error.  An axiom (no body) gets the scheme
       [forall a, a]: its type is not recoverable from λ□.

    3. DATATYPE SIGNATURES FROM THE ENVIRONMENT.  The untyped inductive
       declarations carry constructor names and arities but no field types.
       [init_sigs] gives every inductive block [ind_npars] PARAMETER variables
       (rigid: they never enter the substitution) and every constructor field
       an UNKNOWN.  A constructor use ([tConstruct], the [tCase] branch binders,
       [tProj]) freshens the parameters into INSTANCE variables θ; a known
       field type is instantiated at θ; an unknown field yields a fresh
       variable [v] and a PENDING constraint "field = v at θ".  The type of a
       constructor is  [□ -> … -> □ -> f₁ -> … -> fₙ -> I θ]  with one [□]
       per parameter, matching the erased calling convention (parameters are
       passed as boxes) and the shape typed erasure gives inductive bodies
       (parameter entries typed [TBox] followed by the [cstr_nargs] fields).

       Pending constraints are RESOLVED at the end of each constant, before
       generalization, in this priority order (ties by creation order):
         (0) the field became known meanwhile: ordinary unification;
         (1) PATTERN: the use type mentions instance variables of this use
             (or, by the "regular recursion" rule (b), instance variables of
             the same inductive block from another use, which are first
             identified with this use's θ) — the field is the use type with
             θ abstracted back to the parameters: the unique most general
             solution when the use type mentions only θ;
         (2) FLEX: the use type has free variables — if some θₖ is still
             unsolved, the field IS parameter k and θₖ := use type
             (parameter preference: the most general choice), otherwise the
             field is the use type and its variables become GLOBAL;
         (3) GROUND: as (2) with no variables; [TBox] stays [TBox].
       Rule (b) misfires on a non-recursive inductive nested in itself
       (e.g. [pair x (pair y z)]); when resolution then fails, the constant
       is re-run with rule (b) disabled before the error is reported.

       GENERALIZATION DISCIPLINE.  Field types may mention only their own
       inductive's parameters and global variables; a global variable is one
       that occurs in a field type, or the still-unconstrained type of an
       UNUSED top-level binder of a constant ([pin_unused]: an erased type or
       proof parameter, which typed erasure types [TBox]); globals are never
       generalized by a constant, so later constants (the callers) can still
       solve them.  At emission every unknown field and every unsolved global
       becomes [TBox] — the type typed erasure gives erased content — so no
       dangling variable is ever printed.  Everything else about a constant is
       generalized as usual.

    4. TERMS.  [infer_tm] handles tBox (type [TBox]; a box applied to
       anything stays [TBox], as [□ x → □]), tRel, tLambda, tApp, tLetIn
       (monomorphic), tConst, tConstruct (partial application yields the
       residual arrow), tCase (ONE freshening of the inductive per case node,
       shared by the scrutinee and all branches; a scrutinee of type [TBox] is
       a match on erased content and types its binders [TBox]), tProj, tFix
       (MONOMORPHIC recursion: one fresh variable per fixpoint).  A match
       with an erased ([□]) branch next to a non-erased one is dependent
       elimination and is rejected with a message saying so ([case_result]):
       it is the place where Rocq's OCaml/Haskell extraction inserts a cast
       and typed erasure prints [TAny], and the typed printers cannot
       consume [TAny] (it prints as the unit type).  tCoFix, tEvar, tVar,
       tPrim, tLazy, tForce are rejected: the typed backends cannot print
       them.  Running out of [infer_fuel] (term depth) is an error.

    IMPLEMENTATION NOTE — why [infer_tm] is a SINGLE fuel-bounded [Fixpoint]
    and not a mutual one.  A mutual [Fixpoint] over the term, with recursive
    calls sitting inside [match unify unify_fuel …], forces the guard checker
    to WHNF-reduce [unify] at the *literal* fuel while validating the block,
    which is pathologically slow.  The list traversals ([go_args]/[go_brs]/
    [go_mfix]/[apply_tys]) are ordinary non-mutual [Fixpoint]s over their
    list, parameterised by the term-inference function [f] and by an OPAQUE
    unify fuel [uf]; [infer_tm] recurses structurally on [fuel : nat].

    ------------------------------------------------------------------------
    PIPELINE INTEGRATION.  [PAst.infer_for_backend] wraps [infer] with the
    pipeline-level message; [Pipeline.apply_transforms] runs it on the raw
    environment before the typed pipeline for the typed targets (Rust, Elm,
    [AST LambdaBoxTyped]), and [PAst.PAst_to_ExAst] uses the same function.
    The section lemma guarantees only that the promoted environment erases
    back to the original untyped one. *)

From Stdlib Require Import List Arith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From Peregrine Require Import Utils.

Import ListNotations MonadNotation.
Local Open Scope bs_scope.

(** ** Type-inference substitutions and idempotent unification *)

Definition subst_t := list (nat * ExAst.box_type).

Fixpoint slookup (s : subst_t) (n : nat) : option ExAst.box_type :=
  match s with
  | [] => None
  | (m, t) :: s' => if Nat.eqb n m then Some t else slookup s' n
  end.

(** One structural pass.  Because [extend] keeps the substitution IDEMPOTENT
    (see below), a single pass is a *full* zonk: every reachable variable is
    resolved.  [zonk] doubles as a renaming when [s] maps variables to
    variables. *)
Fixpoint zonk (s : subst_t) (t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar n => match slookup s n with Some u => u | None => ExAst.TVar n end
  | ExAst.TArr a b => ExAst.TArr (zonk s a) (zonk s b)
  | ExAst.TApp a b => ExAst.TApp (zonk s a) (zonk s b)
  | _ => t
  end.

Fixpoint occurs (n : nat) (t : ExAst.box_type) : bool :=
  match t with
  | ExAst.TVar m => Nat.eqb n m
  | ExAst.TArr a b => occurs n a || occurs n b
  | ExAst.TApp a b => occurs n a || occurs n b
  | _ => false
  end.

(** Substitute a single variable [n] by [r] everywhere in [t]. *)
Fixpoint subst_var (n : nat) (r t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar m => if Nat.eqb m n then r else ExAst.TVar m
  | ExAst.TArr a b => ExAst.TArr (subst_var n r a) (subst_var n r b)
  | ExAst.TApp a b => ExAst.TApp (subst_var n r a) (subst_var n r b)
  | _ => t
  end.

(** Idempotency-preserving extension.  [t] is first fully zonked against [s]
    (so it mentions no variable in [dom s]); the occurs-check then rejects a
    cyclic binding; finally the new binding [n ↦ t] is pushed through the
    codomains of every existing binding.  The result is again idempotent, so a
    one-pass [zonk] stays a full zonk. *)
Definition extend (n : nat) (t : ExAst.box_type) (s : subst_t) : option subst_t :=
  let t := zonk s t in
  if occurs n t then None
  else Some ((n, t) :: map (fun '(m, u) => (m, subst_var n t u)) s).

Definition unify_fuel : nat := 1000.

(** Fuel-bounded for structural termination; each recursive descent works on
    zonked (hence idempotent-resolved) types.  [None] is failure (including
    running out of fuel). *)
Fixpoint unify (fuel : nat) (s : subst_t) (a b : ExAst.box_type) : option subst_t :=
  match fuel with
  | 0 => None
  | S fuel =>
    let a := zonk s a in
    let b := zonk s b in
    match a, b with
    | ExAst.TVar n, ExAst.TVar m => if Nat.eqb n m then Some s else extend n b s
    | ExAst.TVar n, _ => extend n b s
    | _, ExAst.TVar m => extend m a s
    | ExAst.TBox, ExAst.TBox => Some s
    | ExAst.TAny, ExAst.TAny => Some s
    | ExAst.TArr a1 a2, ExAst.TArr b1 b2 =>
      match unify fuel s a1 b1 with
      | Some s1 => unify fuel s1 a2 b2
      | None => None
      end
    | ExAst.TApp a1 a2, ExAst.TApp b1 b2 =>
      match unify fuel s a1 b1 with
      | Some s1 => unify fuel s1 a2 b2
      | None => None
      end
    | ExAst.TInd i, ExAst.TInd j => if eq_inductive i j then Some s else None
    | ExAst.TConst c, ExAst.TConst d => if eq_kername c d then Some s else None
    | _, _ => None
    end
  end.

(** ** [box_type] utilities *)

Fixpoint ftv (t : ExAst.box_type) : list nat :=
  match t with
  | ExAst.TVar n => [n]
  | ExAst.TArr a b => (ftv a ++ ftv b)%list
  | ExAst.TApp a b => (ftv a ++ ftv b)%list
  | _ => []
  end.

Fixpoint mkArrows (dom : list ExAst.box_type) (cod : ExAst.box_type) : ExAst.box_type :=
  match dom with
  | [] => cod
  | a :: rest => ExAst.TArr a (mkArrows rest cod)
  end.

Fixpoint mem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | m :: l' => if Nat.eqb n m then true else mem_nat n l'
  end.

Fixpoint dedup_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' => if mem_nat n (dedup_nat l') then dedup_nat l' else n :: dedup_nat l'
  end.

Fixpoint idx_nat (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | m :: l' => if Nat.eqb n m then 0 else S (idx_nat n l')
  end.

Fixpoint remove_all (l rem : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' => if mem_nat n rem then remove_all l' rem else n :: remove_all l' rem
  end.

(** Rename the listed variables to their position in the list; every other
    variable becomes [TBox].  Used at emission: bound variables of a scheme
    become [0 .. k-1], parameters of an inductive become [0 .. npars-1], and
    nothing else survives (see the module header, GENERALIZATION DISCIPLINE). *)
Fixpoint rename_or_box (vs : list nat) (t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar n => if mem_nat n vs then ExAst.TVar (idx_nat n vs) else ExAst.TBox
  | ExAst.TArr a b => ExAst.TArr (rename_or_box vs a) (rename_or_box vs b)
  | ExAst.TApp a b => ExAst.TApp (rename_or_box vs a) (rename_or_box vs b)
  | _ => t
  end.

Fixpoint string_of_bt (t : ExAst.box_type) : string :=
  match t with
  | ExAst.TBox => "box"
  | ExAst.TAny => "any"
  | ExAst.TArr a b => "(" ++ string_of_bt a ++ " -> " ++ string_of_bt b ++ ")"
  | ExAst.TApp a b => "(" ++ string_of_bt a ++ " " ++ string_of_bt b ++ ")"
  | ExAst.TVar n => "?" ++ string_of_nat n
  | ExAst.TInd i => string_of_kername i.(inductive_mind)
  | ExAst.TConst k => string_of_kername k
  end.

(** ** Damas–Milner type schemes and the cross-constant scheme table

    A scheme lists its bound variables (by their global number) and keeps the
    body in the global numbering; free variables of the body are GLOBAL
    variables (see the module header).  [instantiate] renames the bound
    variables into the fresh region starting at [base] and leaves the globals
    alone. *)

Definition scheme : Type := (list nat * ExAst.box_type)%type.
Definition sch_env : Type := list (kername * scheme).

Fixpoint sch_lookup (E : sch_env) (kn : kername) : option scheme :=
  match E with
  | [] => None
  | (kn', sch) :: E' => if eq_kername kn kn' then Some sch else sch_lookup E' kn
  end.

Definition renaming (vs : list nat) (base : nat) : subst_t :=
  combine vs (map (fun i => ExAst.TVar (base + i)) (seq 0 (length vs))).

Definition instantiate (base : nat) (sch : scheme) : ExAst.box_type * nat :=
  let '(vs, body) := sch in (zonk (renaming vs base) body, base + length vs).

(** ** Datatype signatures reconstructed from the environment

    [fields] is one constructor's field types (one per [cstr_nargs], NOT
    including the parameters), [None] while unknown.  Known fields are stated
    over the block's parameter variables [is_params] (global numbers that are
    never bound) and possibly global variables. *)

Definition fields : Type := list (option ExAst.box_type).

Record ind_sig := mk_ind_sig {
  is_npars : nat;
  is_params : list nat;
  is_ctors : list (list fields)  (* per inductive body, per constructor *)
}.

Definition sig_table : Type := list (kername * ind_sig).

Fixpoint sig_lookup (T : sig_table) (kn : kername) : option ind_sig :=
  match T with
  | [] => None
  | (kn', sg) :: T' => if eq_kername kn kn' then Some sg else sig_lookup T' kn
  end.

Definition sig_fields (T : sig_table) (ind : inductive) (c : nat) : option (ind_sig * fields) :=
  match sig_lookup T ind.(inductive_mind) with
  | None => None
  | Some sg =>
    match nth_error sg.(is_ctors) ind.(inductive_ind) with
    | None => None
    | Some ctors => match nth_error ctors c with
                   | None => None
                   | Some fs => Some (sg, fs)
                   end
    end
  end.

Fixpoint set_nth {A} (l : list A) (i : nat) (f : A -> A) : list A :=
  match l, i with
  | [], _ => []
  | x :: l', 0 => f x :: l'
  | x :: l', S i' => x :: set_nth l' i' f
  end.

Fixpoint sig_update (T : sig_table) (kn : kername) (f : ind_sig -> ind_sig) : sig_table :=
  match T with
  | [] => []
  | (kn', sg) :: T' => if eq_kername kn kn' then (kn', f sg) :: T' else (kn', sg) :: sig_update T' kn f
  end.

Definition sig_set_field (T : sig_table) (ind : inductive) (c j : nat) (ty : ExAst.box_type) : sig_table :=
  sig_update T ind.(inductive_mind)
    (fun sg => {| is_npars := sg.(is_npars); is_params := sg.(is_params);
                  is_ctors := set_nth sg.(is_ctors) ind.(inductive_ind)
                                (fun ctors => set_nth ctors c
                                   (fun fs => set_nth fs j (fun _ => Some ty))) |}).

Definition sig_map (f : ExAst.box_type -> ExAst.box_type) (T : sig_table) : sig_table :=
  map (fun '(kn, sg) =>
         (kn, {| is_npars := sg.(is_npars); is_params := sg.(is_params);
                 is_ctors := map (map (map (option_map f))) sg.(is_ctors) |})) T.

(** Free variables of all known fields: the GLOBAL variables (parameters
    included, harmlessly: they never occur in a term's type). *)
Definition sig_ftv (T : sig_table) : list nat :=
  flat_map (fun '(_, sg) =>
              flat_map (flat_map (flat_map (fun f => match f with Some t => ftv t | None => [] end)))
                       sg.(is_ctors)) T.

(** Allocate the parameter variables and unknown fields of every inductive
    block of [Σ]; returns the table and the next fresh variable. *)
Fixpoint init_sigs (Σ : EAst.global_context) (cnt : nat) : sig_table * nat :=
  match Σ with
  | [] => ([], cnt)
  | (kn, EAst.InductiveDecl mib) :: Σ' =>
    let '(T, cnt1) := init_sigs Σ' cnt in
    let np := mib.(EAst.ind_npars) in
    let sg := {| is_npars := np;
                 is_params := seq cnt1 np;
                 is_ctors := map (fun oib => map (fun c => repeat None c.(EAst.cstr_nargs))
                                                 oib.(EAst.ind_ctors))
                                 mib.(EAst.ind_bodies) |} in
    ((kn, sg) :: T, cnt1 + np)
  | (_, EAst.ConstantDecl _) :: Σ' => init_sigs Σ' cnt
  end.

(** ** Inference state *)

(** "Field [pd_fld] of constructor [pd_ctor] of [pd_ind] has type [pd_var] at
    the instance [pd_theta]" — a constraint on a still-unknown field. *)
Record pending := mk_pending {
  pd_ind : inductive; pd_ctor : nat; pd_fld : nat; pd_theta : list nat; pd_var : nat }.

Record st := mk_st {
  st_cnt : nat;                                (* next fresh variable *)
  st_s : subst_t;                              (* idempotent substitution *)
  st_pend : list pending;                      (* in creation order *)
  st_inst : list (nat * (kername * nat));      (* instance var ↦ (block, parameter index) *)
  st_glob : list nat;                          (* pinned globals: unused-binder types, see [pin_unused] *)
  st_taken : list nat                          (* instance vars a field has been assigned to, see [resolve_one] *)
}.

Definition fresh (ss : st) : nat * st :=
  (ss.(st_cnt), {| st_cnt := S (st_cnt ss); st_s := ss.(st_s); st_pend := ss.(st_pend); st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |}).

Definition with_s (ss : st) (s : subst_t) : st :=
  {| st_cnt := ss.(st_cnt); st_s := s; st_pend := ss.(st_pend); st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |}.

Definition add_pending (ss : st) (p : pending) : st :=
  {| st_cnt := ss.(st_cnt); st_s := ss.(st_s); st_pend := (ss.(st_pend) ++ [p])%list; st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |}.

Definition add_insts (ss : st) (kn : kername) (theta : list nat) : st :=
  {| st_cnt := ss.(st_cnt); st_s := ss.(st_s); st_pend := ss.(st_pend);
     st_inst := (combine theta (map (fun k => (kn, k)) (seq 0 (length theta))) ++ ss.(st_inst))%list;
     st_glob := ss.(st_glob); st_taken := ss.(st_taken) |}.

Definition reset_local (ss : st) : st :=
  {| st_cnt := ss.(st_cnt); st_s := ss.(st_s); st_pend := []; st_inst := []; st_glob := ss.(st_glob); st_taken := [] |}.

Fixpoint inst_lookup (l : list (nat * (kername * nat))) (n : nat) : option (kername * nat) :=
  match l with
  | [] => None
  | (m, r) :: l' => if Nat.eqb n m then Some r else inst_lookup l' n
  end.

Definition zonk_st (ss : st) (t : ExAst.box_type) : ExAst.box_type := zonk ss.(st_s) t.

(** Unification in the state, as a [result'].  [uf] is the (opaque) unify fuel,
    see the implementation note in the header. *)
Definition unify_st (uf : nat) (ss : st) (a b : ExAst.box_type) : result' st :=
  match unify uf ss.(st_s) a b with
  | Some s => Ok (with_s ss s)
  | None => Err ("cannot unify " ++ string_of_bt (zonk_st ss a) ++ " with " ++ string_of_bt (zonk_st ss b))
  end.

(** Freshen the parameters of the block of [ind]: the instance variables θ. *)
Definition fresh_theta (ss : st) (ind : inductive) (np : nat) : list nat * st :=
  let theta := seq ss.(st_cnt) np in
  let S1 := {| st_cnt := ss.(st_cnt) + np; st_s := ss.(st_s); st_pend := ss.(st_pend); st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |} in
  (theta, add_insts S1 ind.(inductive_mind) theta).

Definition param_subst (params theta : list nat) : subst_t :=
  combine params (map ExAst.TVar theta).

(** The field types of constructor [c] of [ind] at the instance [theta]: known
    fields are instantiated, unknown ones become fresh variables with a
    pending constraint. *)
Fixpoint fields_at (ss : st) (ind : inductive) (c : nat) (params theta : list nat)
                   (fs : fields) (j : nat) : list ExAst.box_type * st :=
  match fs with
  | [] => ([], ss)
  | Some ty :: fs' =>
    let '(rest, S1) := fields_at ss ind c params theta fs' (S j) in
    (zonk (param_subst params theta) ty :: rest, S1)
  | None :: fs' =>
    let '(v, S1) := fresh ss in
    let S2 := add_pending S1 {| pd_ind := ind; pd_ctor := c; pd_fld := j; pd_theta := theta; pd_var := v |} in
    let '(rest, S3) := fields_at S2 ind c params theta fs' (S j) in
    (ExAst.TVar v :: rest, S3)
  end.

Definition ind_at (ind : inductive) (theta : list nat) : ExAst.box_type :=
  ExAst.mkTApps (ExAst.TInd ind) (map ExAst.TVar theta).

Definition err_ctor (ind : inductive) (c : nat) : string :=
  "constructor " ++ string_of_nat c ++ " of " ++ string_of_kername ind.(inductive_mind) ++ " is not declared".

(** The type of a constructor at a fresh instance: one [TBox] per parameter,
    the fields, then the inductive at the instance. *)
Definition ctor_type (T : sig_table) (ss : st) (ind : inductive) (c : nat) : result' (ExAst.box_type * st) :=
  match sig_fields T ind c with
  | None => Err (err_ctor ind c)
  | Some (sg, fs) =>
    let '(theta, S1) := fresh_theta ss ind sg.(is_npars) in
    let '(ftys, S2) := fields_at S1 ind c sg.(is_params) theta fs 0 in
    Ok (mkArrows (repeat ExAst.TBox sg.(is_npars) ++ ftys)%list (ind_at ind theta), S2)
  end.

(** ** Algorithm-W-style term inference *)

Definition tm_fn : Type := list ExAst.box_type -> st -> EAst.term -> result' (ExAst.box_type * st).

Fixpoint go_args (f : tm_fn) (ctx : list ExAst.box_type) (ss : st) (ts : list EAst.term) {struct ts}
                 : result' (list ExAst.box_type * st) :=
  match ts with
  | [] => Ok ([], ss)
  | u :: us =>
    '(tu, S1) <- f ctx ss u;;
    '(rest, S2) <- go_args f ctx S1 us;;
    Ok (tu :: rest, S2)
  end.

(** Apply a function type to argument types, left to right.  A [TBox] head
    absorbs its arguments ([□ x → □]). *)
Fixpoint apply_tys (uf : nat) (ss : st) (fty : ExAst.box_type) (args : list ExAst.box_type) {struct args}
                   : result' (ExAst.box_type * st) :=
  match args with
  | [] => Ok (fty, ss)
  | a :: args' =>
    match zonk_st ss fty with
    | ExAst.TBox => Ok (ExAst.TBox, ss)
    | fty' =>
      let '(r, S1) := fresh ss in
      S2 <- unify_st uf S1 fty' (ExAst.TArr a (ExAst.TVar r));;
      apply_tys uf S2 (zonk_st S2 (ExAst.TVar r)) args'
    end
  end.

(** Infer all [tCase] branches and return their (zonked) body types.  Branch
    binders get the constructor's field types at the case's instance [theta]
    ([erased = true]: scrutinee of type [TBox], all binders [TBox]).  [bi] is
    the branch/constructor index. *)
Fixpoint go_brs (uf : nat) (f : tm_fn) (T : sig_table)
                (ctx : list ExAst.box_type) (ind : inductive) (theta : list nat) (erased : bool)
                (bs : list (list name * EAst.term)) (bi : nat) (ss : st) {struct bs}
                : result' (list ExAst.box_type * st) :=
  match bs with
  | [] => Ok ([], ss)
  | (nms, body) :: bs' =>
    '(btys, S1) <-
      (if erased then Ok (map (fun _ => ExAst.TBox) nms, ss)
       else match sig_fields T ind bi with
            | None => Err (err_ctor ind bi)
            | Some (sg, fs) =>
              if Nat.eqb (length fs) (length nms)
              then Ok (fields_at ss ind bi sg.(is_params) theta fs 0)
              else Err ("branch " ++ string_of_nat bi ++ " of a match on "
                        ++ string_of_kername ind.(inductive_mind) ++ " binds "
                        ++ string_of_nat (length nms) ++ " variables, the constructor has "
                        ++ string_of_nat (length fs) ++ " arguments")
            end);;
    '(tbody, S2) <- f (rev btys ++ ctx)%list S1 body;;
    '(rest, S3) <- go_brs uf f T ctx ind theta erased bs' (S bi) S2;;
    Ok (zonk_st S3 tbody :: rest, S3)
  end.

Fixpoint unify_all (uf : nat) (ss : st) (r : ExAst.box_type) (tys : list ExAst.box_type) : result' st :=
  match tys with
  | [] => Ok ss
  | t :: tys' => S1 <- unify_st uf ss t r;; unify_all uf S1 r tys'
  end.

Definition is_box (t : ExAst.box_type) : bool :=
  match t with ExAst.TBox => true | _ => false end.

(** The result type of a match from its branch types.  A branch whose body is
    [□] while another is not is DEPENDENT ELIMINATION (an absurd case, or a
    branch returning a proof or type): the erased branch carries no type, and
    unifying it with the others would silently equate real types with [□].
    This is exactly where Rocq's OCaml/Haskell extraction inserts
    [Obj.magic]/[unsafeCoerce] and where typed erasure prints [TAny]; the
    typed printers have no cast to offer, so it is an error here. *)
Definition case_result (uf : nat) (ss : st) (ind : inductive) (r : ExAst.box_type)
           (tys : list ExAst.box_type) : result' st :=
  let nb := length (filter is_box tys) in
  if Nat.eqb nb 0 then unify_all uf ss r tys
  else if Nat.eqb nb (length tys) then unify_st uf ss r ExAst.TBox
  else Err ("a match on " ++ string_of_kername ind.(inductive_mind)
            ++ " has an erased (box) branch next to a non-erased one: dependent elimination"
            ++ " is not typable without an unchecked cast (typed erasure would print TAny here)").

(** Infer a (monomorphic) mutual fixpoint: each body is checked in the context
    extended with the fixpoint variables [vars] and unified against its own
    variable. *)
Fixpoint go_mfix (uf : nat) (f : tm_fn) (ctx : list ExAst.box_type) (vars : list ExAst.box_type)
                 (ss : st) (ds : list (EAst.def EAst.term)) {struct ds} : result' st :=
  match ds, vars with
  | d :: ds', v :: vs' =>
    '(tb, S1) <- f ctx ss d.(EAst.dbody);;
    S2 <- unify_st uf S1 tb v;;
    go_mfix uf f ctx vs' S2 ds'
  | _, _ => Ok ss
  end.

Fixpoint infer_tm (fuel : nat) (T : sig_table) (E : sch_env)
                  (ctx : list ExAst.box_type) (ss : st) (t : EAst.term) {struct fuel}
                  : result' (ExAst.box_type * st) :=
  match fuel with
  | 0 => Err "term too deep for type inference"
  | S fuel =>
    match t with
    | EAst.tBox => Ok (ExAst.TBox, ss)
    | EAst.tRel n =>
      match nth_error ctx n with
      | Some ty => Ok (zonk_st ss ty, ss)
      | None => Err ("unbound variable " ++ string_of_nat n)
      end
    | EAst.tLambda _ body =>
      let '(a, S1) := fresh ss in
      '(rb, S2) <- infer_tm fuel T E (ExAst.TVar a :: ctx) S1 body;;
      Ok (ExAst.TArr (zonk_st S2 (ExAst.TVar a)) rb, S2)
    | EAst.tApp u v =>
      '(tu, S1) <- infer_tm fuel T E ctx ss u;;
      '(tv, S2) <- infer_tm fuel T E ctx S1 v;;
      apply_tys unify_fuel S2 tu [tv]
    | EAst.tLetIn _ b body =>
      '(tb, S1) <- infer_tm fuel T E ctx ss b;;
      infer_tm fuel T E (zonk_st S1 tb :: ctx) S1 body
    | EAst.tConst kn =>
      match sch_lookup E kn with
      | Some sch => let '(ty, c1) := instantiate ss.(st_cnt) sch in
                    Ok (ty, {| st_cnt := c1; st_s := ss.(st_s); st_pend := ss.(st_pend); st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |})
      | None => Err ("constant " ++ string_of_kername kn ++ " is used before its declaration")
      end
    | EAst.tConstruct ind c args =>
      '(cty, S1) <- ctor_type T ss ind c;;
      '(atys, S2) <- go_args (infer_tm fuel T E) ctx S1 args;;
      apply_tys unify_fuel S2 cty atys
    | EAst.tCase indn c brs =>
      let ind := fst indn in
      '(tc, S1) <- infer_tm fuel T E ctx ss c;;
      np <- match sig_lookup T ind.(inductive_mind) with
            | Some sg => Ok sg.(is_npars)
            | None => Err ("inductive " ++ string_of_kername ind.(inductive_mind) ++ " is not declared")
            end;;
      let '(theta, S2) := fresh_theta S1 ind np in
      let erased := match zonk_st S2 tc with ExAst.TBox => true | _ => false end in
      S3 <- (if erased then Ok S2 else unify_st unify_fuel S2 tc (ind_at ind theta));;
      let '(r, S4) := fresh S3 in
      '(tys, S5) <- go_brs unify_fuel (infer_tm fuel T E) T ctx ind theta erased brs 0 S4;;
      S6 <- case_result unify_fuel S5 ind (ExAst.TVar r) tys;;
      Ok (zonk_st S6 (ExAst.TVar r), S6)
    | EAst.tProj p c =>
      let ind := p.(proj_ind) in
      '(tc, S1) <- infer_tm fuel T E ctx ss c;;
      match sig_fields T ind 0 with
      | None => Err (err_ctor ind 0)
      | Some (sg, fs) =>
        let '(theta, S2) := fresh_theta S1 ind sg.(is_npars) in
        S3 <- unify_st unify_fuel S2 tc (ind_at ind theta);;
        let '(ftys, S4) := fields_at S3 ind 0 sg.(is_params) theta fs 0 in
        match nth_error ftys p.(proj_arg) with
        | Some ty => Ok (zonk_st S4 ty, S4)
        | None => Err ("projection " ++ string_of_nat p.(proj_arg) ++ " of "
                       ++ string_of_kername ind.(inductive_mind) ++ " is out of range")
        end
      end
    | EAst.tFix mfix idx =>
      let n := length mfix in
      let vars := map ExAst.TVar (seq ss.(st_cnt) n) in
      let S1 := {| st_cnt := ss.(st_cnt) + n; st_s := ss.(st_s); st_pend := ss.(st_pend); st_inst := ss.(st_inst); st_glob := ss.(st_glob); st_taken := ss.(st_taken) |} in
      S2 <- go_mfix unify_fuel (infer_tm fuel T E) (rev vars ++ ctx)%list vars S1 mfix;;
      Ok (zonk_st S2 (nth idx vars ExAst.TBox), S2)
    | EAst.tCoFix _ _ => Err "cofixpoints are not supported by the typed backends"
    | EAst.tEvar _ _ => Err "evars are not supported by the typed backends"
    | EAst.tVar _ => Err "named variables are not supported by the typed backends"
    | EAst.tPrim _ => Err "primitive values are not supported by the typed backends"
    | EAst.tLazy _ | EAst.tForce _ => Err "lazy/force are not supported by the typed backends"
    end
  end.

(** Fuel for [infer_tm]: a bound on the syntactic depth of a constant body.
    Nested [S (S (… O))] literals are the deepest terms in practice. *)
Definition infer_fuel : nat := 4000.

(** ** Resolving the pending field constraints of one constant *)

(** The instance variables of [theta] that are still unsolved, as
    [(parameter index, variable)]. *)
Fixpoint unsolved_theta (s : subst_t) (theta : list nat) (k : nat) : list (nat * nat) :=
  match theta with
  | [] => []
  | th :: theta' =>
    match zonk s (ExAst.TVar th) with
    | ExAst.TVar v => (k, v) :: unsolved_theta s theta' (S k)
    | _ => unsolved_theta s theta' (S k)
    end
  end.

(** Rule (b): identify every instance variable of the same block occurring in
    [vars] (and not one of this use's own instance variables) with the
    corresponding variable of [theta]. *)
Fixpoint identify_insts (uf : nat) (ss : st) (kn : kername) (theta : list nat) (vars : list nat)
         : result' st :=
  match vars with
  | [] => Ok ss
  | x :: vars' =>
    match inst_lookup ss.(st_inst) x with
    | Some (kn', k) =>
      if eq_kername kn kn' && negb (mem_nat x theta)
      then match nth_error theta k with
           | Some th => S1 <- unify_st uf ss (ExAst.TVar x) (ExAst.TVar th);; identify_insts uf S1 kn theta vars'
           | None => identify_insts uf ss kn theta vars'
           end
      else identify_insts uf ss kn theta vars'
    | None => identify_insts uf ss kn theta vars'
    end
  end.

Definition class_of (T : sig_table) (ss : st) (p : pending) : nat :=
  match sig_fields T p.(pd_ind) p.(pd_ctor) with
  | Some (_, fs) =>
    match nth_error fs p.(pd_fld) with
    | Some (Some _) => 0
    | _ =>
      let sigma := zonk_st ss (ExAst.TVar p.(pd_var)) in
      let fv := ftv sigma in
      let thv := map snd (unsolved_theta ss.(st_s) p.(pd_theta) 0) in
      if existsb (fun x => mem_nat x thv
                           || match inst_lookup ss.(st_inst) x with
                              | Some (kn, _) => eq_kername kn p.(pd_ind).(inductive_mind)
                              | None => false
                              end) fv
      then 1
      else match fv with [] => 3 | _ => 2 end
    end
  | None => 0
  end.

(** First pending constraint of class [c], and the others. *)
Fixpoint pick_class (T : sig_table) (ss : st) (c : nat) (ps : list pending)
         : option (pending * list pending) :=
  match ps with
  | [] => None
  | p :: ps' =>
    if Nat.eqb (class_of T ss p) c then Some (p, ps')
    else match pick_class T ss c ps' with
         | Some (q, rest) => Some (q, p :: rest)
         | None => None
         end
  end.

Definition pick (T : sig_table) (ss : st) (ps : list pending) : option (pending * list pending) :=
  match pick_class T ss 0 ps with
  | Some r => Some r
  | None =>
    match pick_class T ss 1 ps with
    | Some r => Some r
    | None =>
      match pick_class T ss 2 ps with
      | Some r => Some r
      | None => pick_class T ss 3 ps
      end
    end
  end.

Definition resolve_one (uf : nat) (rule_b : bool) (T : sig_table) (ss : st) (p : pending)
           : result' (sig_table * st) :=
  match sig_fields T p.(pd_ind) p.(pd_ctor) with
  | None => Err (err_ctor p.(pd_ind) p.(pd_ctor))
  | Some (sg, fs) =>
    match nth_error fs p.(pd_fld) with
    | Some (Some ty) =>
      S1 <- unify_st uf ss (zonk (param_subst sg.(is_params) p.(pd_theta)) ty) (ExAst.TVar p.(pd_var));;
      Ok (T, S1)
    | _ =>
      let kn := p.(pd_ind).(inductive_mind) in
      S1 <- (if rule_b
             then identify_insts uf ss kn p.(pd_theta) (ftv (zonk_st ss (ExAst.TVar p.(pd_var))))
             else Ok ss);;
      let sigma := zonk_st S1 (ExAst.TVar p.(pd_var)) in
      let unsolved := unsolved_theta S1.(st_s) p.(pd_theta) 0 in
      let thv := map snd unsolved in
      let abstract := zonk (map (fun '(k, v) => (v, ExAst.TVar (nth k sg.(is_params) 0))) unsolved) in
      (* parameters still available for rule (2)/(3): unsolved and not yet
         assigned to another field of this use (an instance variable bound to
         a VARIABLE still zonks to a variable, so "unsolved" alone would let
         two fields share one parameter) *)
      let avail := filter (fun '(k, _) => negb (mem_nat (nth k p.(pd_theta) 0) S1.(st_taken))) unsolved in
      let set ty S' := Ok (sig_set_field T p.(pd_ind) p.(pd_ctor) p.(pd_fld) ty, S') in
      match sigma with
      | ExAst.TBox => set ExAst.TBox S1
      | _ =>
        if existsb (fun x => mem_nat x thv) (ftv sigma)
        then set (abstract sigma) S1                      (* (1) pattern *)
        else match avail with
             | (k, v) :: _ =>                              (* (2)/(3) parameter preference *)
               S2 <- unify_st uf S1 (ExAst.TVar v) sigma;;
               let S3 := {| st_cnt := S2.(st_cnt); st_s := S2.(st_s); st_pend := S2.(st_pend); st_inst := S2.(st_inst);
                            st_glob := S2.(st_glob); st_taken := nth k p.(pd_theta) 0 :: S2.(st_taken) |} in
               set (ExAst.TVar (nth k sg.(is_params) 0)) S3
             | [] => set sigma S1                          (* (2)/(3) no parameter left *)
             end
      end
    end
  end.

Fixpoint resolve (fuel : nat) (uf : nat) (rule_b : bool) (T : sig_table) (ss : st) (ps : list pending)
         : result' (sig_table * st) :=
  match fuel with
  | 0 => Ok (T, ss)
  | S fuel =>
    match pick T ss ps with
    | None => Ok (T, ss)
    | Some (p, rest) =>
      '(T1, S1) <- resolve_one uf rule_b T ss p;;
      resolve fuel uf rule_b T1 S1 rest
    end
  end.

(** ** Per-constant inference and generalization *)

(** Generalize a zonked type over its free variables except the globals [G]. *)
Definition generalize (G : list nat) (t : ExAst.box_type) : scheme :=
  (remove_all (dedup_nat (ftv t)) G, t).

(** Does de Bruijn index [k] occur in [t]?  [true] when unsure (primitives). *)
Fixpoint rel_used (k : nat) (t : EAst.term) : bool :=
  match t with
  | EAst.tRel n => Nat.eqb n k
  | EAst.tBox | EAst.tVar _ | EAst.tConst _ => false
  | EAst.tEvar _ args => existsb (rel_used k) args
  | EAst.tLambda _ b => rel_used (S k) b
  | EAst.tLetIn _ b b' => rel_used k b || rel_used (S k) b'
  | EAst.tApp u v => rel_used k u || rel_used k v
  | EAst.tConstruct _ _ args => existsb (rel_used k) args
  | EAst.tCase _ c brs => rel_used k c || existsb (fun '(nms, b) => rel_used (length nms + k) b) brs
  | EAst.tProj _ c => rel_used k c
  | EAst.tFix mfix _ | EAst.tCoFix mfix _ => existsb (fun d => rel_used (length mfix + k) d.(EAst.dbody)) mfix
  | EAst.tPrim _ => true
  | EAst.tLazy u | EAst.tForce u => rel_used k u
  end.

(** The still-unconstrained types of UNUSED top-level binders of a constant.
    An unused binder whose type is still a variable at generalization time is
    almost always an erased type or proof parameter (typed erasure gives it
    [TBox]); generalizing it instead leaves a type variable that the typed
    pipeline's argument removal orphans (Rust then needs an annotation).  These
    variables are PINNED: never generalized, left for the callers to solve
    (every caller passing a box makes them [TBox]), and [TBox] at emission if
    nothing did. *)
Fixpoint pin_unused (s : subst_t) (t : EAst.term) (ty : ExAst.box_type) : list nat :=
  match t, ty with
  | EAst.tLambda _ b, ExAst.TArr d c =>
    (match zonk s d with
     | ExAst.TVar v => if rel_used 0 b then [] else [v]
     | _ => []
     end ++ pin_unused s b c)%list
  | _, _ => []
  end.

Definition infer_const_once (rule_b : bool) (T : sig_table) (E : sch_env) (ss : st) (t : EAst.term)
           : result' (scheme * sig_table * st) :=
  '(ty, S1) <- infer_tm infer_fuel T E [] (reset_local ss) t;;
  '(T2, S2) <- resolve (length S1.(st_pend)) unify_fuel rule_b T S1 S1.(st_pend);;
  let T3 := sig_map (zonk S2.(st_s)) T2 in
  let ty' := zonk_st S2 ty in
  let pinned := pin_unused S2.(st_s) t ty' in
  let S3 := {| st_cnt := S2.(st_cnt); st_s := S2.(st_s); st_pend := S2.(st_pend); st_inst := S2.(st_inst);
               st_glob := (pinned ++ S2.(st_glob))%list; st_taken := S2.(st_taken) |} in
  Ok (generalize (sig_ftv T3 ++ S3.(st_glob))%list ty', T3, S3).

(** Rename the parameters of every block by [ren]. *)
Definition sig_rename (ren : subst_t) (glob : list nat) (T : sig_table) : sig_table :=
  map (fun '(kn, sg) =>
         (kn, {| is_npars := sg.(is_npars);
                 is_params := map (fun v => idx_nat v glob) sg.(is_params);
                 is_ctors := map (map (map (option_map (zonk ren)))) sg.(is_ctors) |})) T.

(** After a constant: zonk every persistent structure, then RENUMBER.  The
    surviving free variables (parameters, globals in field types, pinned
    binders, free variables of schemes) become [0 .. g-1]; the bound variables
    of every scheme become [g .. g+k-1] (schemes are independent, so they may
    share that range); the fresh counter restarts at [g] and the substitution
    is dropped.  Variable numbers thus stay proportional to the size of ONE
    constant.  This matters because [nat] extracts to Peano numerals here:
    comparing variable numbers costs time linear in their size.
    ponytail: within a constant the cost is still ~cubic in its size for a
    long chain of constructor applications (a 1000-deep [S] literal takes
    seconds); a positional substitution would make it quadratic. *)
Definition compact (T : sig_table) (E : sch_env) (ss : st) : sig_table * sch_env * st :=
  let z := zonk ss.(st_s) in
  (* A scheme's bound numbers may coincide with fresh variables of the constant
     just processed (both ranges start at the previous [g]); protect them with
     identity bindings so only the globals of the body get zonked. *)
  let E1 := map (fun '(k, (vs, b)) => (k, (vs, zonk (combine vs (map ExAst.TVar vs) ++ ss.(st_s))%list b))) E in
  let T1 := sig_map z T in
  let pinned := flat_map (fun v => match z (ExAst.TVar v) with ExAst.TVar v' => [v'] | _ => [] end) ss.(st_glob) in
  let glob := dedup_nat (flat_map (fun '(_, sg) => sg.(is_params)) T1 ++ sig_ftv T1 ++ pinned
                         ++ flat_map (fun '(_, (vs, b)) => remove_all (ftv b) vs) E1)%list in
  let g := length glob in
  let ren := combine glob (map ExAst.TVar (seq 0 g)) in
  (* Bound variables first: an old scheme's bound numbers may coincide with
     fresh numbers of the constant just processed. *)
  let E2 := map (fun '(k, (vs, b)) =>
                   (k, (seq g (length vs),
                        zonk (combine vs (map ExAst.TVar (seq g (length vs))) ++ ren)%list b))) E1 in
  (sig_rename ren glob T1, E2,
   {| st_cnt := g; st_s := []; st_pend := []; st_inst := [];
      st_glob := map (fun v => idx_nat v glob) pinned; st_taken := [] |}).

(** Infer one constant: with rule (b), then without it if that failed.  The
    result includes the constant's scheme in the table, and the state is
    [compact]ed: every variable that survives is either bound by a scheme
    (never unified again, [instantiate] renames it) or global. *)
Definition infer_const (T : sig_table) (E : sch_env) (ss : st) (kn : kername) (body : option EAst.term)
           : result' (sig_table * sch_env * st) :=
  match body with
  | None =>
    let '(a, S1) := fresh ss in
    Ok (T, (kn, ([a], ExAst.TVar a)) :: E, S1)
  | Some t =>
    '(sch, T1, S1) <-
      map_error (fun e => "in constant " ++ string_of_kername kn ++ ": " ++ e)
        (match infer_const_once true T E ss t with
         | Ok r => Ok r
         | Err _ => infer_const_once false T E ss t
         end);;
    Ok (compact T1 ((kn, sch) :: E) S1)
  end.

(** The scheme table in dependency order: [infer_go] recurses on the TAIL
    first (an extracted environment lists a declaration before the
    declarations it depends on). *)
Fixpoint infer_go (Σ : EAst.global_context) (T : sig_table) (ss : st)
         : result' (sig_table * sch_env * st) :=
  match Σ with
  | [] => Ok (T, [], ss)
  | (kn, d) :: Σ' =>
    '(T1, E1, S1) <- infer_go Σ' T ss;;
    match d with
    | EAst.ConstantDecl cb => infer_const T1 E1 S1 kn cb.(EAst.cst_body)
    | EAst.InductiveDecl _ => Ok (T1, E1, S1)
    end
  end.

(** ** Emission: decorating the declarations (the actual forward map) *)

Definition emit_scheme (sch : scheme) : list name * ExAst.box_type :=
  let '(vs, body) := sch in (map (fun _ => nAnon) vs, rename_or_box vs body).

Definition emit_const (E : sch_env) (kn : kername) (cb : EAst.constant_body) : ExAst.constant_body :=
  {| ExAst.cst_type := match sch_lookup E kn with
                       | Some sch => emit_scheme sch
                       | None => ([], ExAst.TBox)
                       end;
     ExAst.cst_body := cb.(EAst.cst_body) |}.

Definition emit_field (params : list nat) (f : option ExAst.box_type) : ExAst.box_type :=
  match f with
  | Some ty => rename_or_box params ty
  | None => ExAst.TBox
  end.

Definition tvar_info : ExAst.type_var_info :=
  {| ExAst.tvar_name := nAnon; ExAst.tvar_is_logical := false; ExAst.tvar_is_arity := true; ExAst.tvar_is_sort := true |}.

(** The field list of a constructor: one [TBox] entry per parameter, then the
    [cstr_nargs] fields.  [cstr_nargs] itself is preserved so that
    [trans_oib] recovers the untyped body exactly. *)
Definition emit_ctor (params : list nat) (c : EAst.constructor_body) (fs : option fields)
  : ident * list (name * ExAst.box_type) * nat :=
  let fs := match fs with Some fs => fs | None => repeat None c.(EAst.cstr_nargs) end in
  (c.(EAst.cstr_name),
   (repeat (nAnon, ExAst.TBox) (length params) ++ map (fun f => (nAnon, emit_field params f)) fs)%list,
   c.(EAst.cstr_nargs)).

(** One inductive body given its block's parameters and (per constructor)
    field table.  Projection [j] is field [j] of constructor 0. *)
Definition emit_oib_aux (params : list nat) (ctors : list fields)
  (oib : EAst.one_inductive_body) : ExAst.one_inductive_body :=
  let fields0 := match nth_error ctors 0 with Some fs => fs | None => [] end in
  {| ExAst.ind_name := oib.(EAst.ind_name);
     ExAst.ind_propositional := oib.(EAst.ind_propositional);
     ExAst.ind_kelim := oib.(EAst.ind_kelim);
     ExAst.ind_type_vars := map (fun _ => tvar_info) params;
     ExAst.ind_ctors := mapi (fun c cb => emit_ctor params cb (nth_error ctors c)) oib.(EAst.ind_ctors);
     ExAst.ind_projs := mapi (fun j p => (p.(EAst.proj_name),
                                           emit_field params (match nth_error fields0 j with
                                                              | Some f => f | None => None end)))
                             oib.(EAst.ind_projs) |}.

Definition emit_oib (T : sig_table) (kn : kername) (i : nat) (oib : EAst.one_inductive_body)
  : ExAst.one_inductive_body :=
  match sig_lookup T kn with
  | Some sg => emit_oib_aux sg.(is_params)
                 (match nth_error sg.(is_ctors) i with Some cs => cs | None => [] end) oib
  | None => emit_oib_aux [] [] oib
  end.

Definition emit_mib (T : sig_table) (kn : kername) (mib : EAst.mutual_inductive_body)
  : ExAst.mutual_inductive_body :=
  {| ExAst.ind_finite := mib.(EAst.ind_finite);
     ExAst.ind_npars := mib.(EAst.ind_npars);
     ExAst.ind_bodies := mapi (emit_oib T kn) mib.(EAst.ind_bodies) |}.

Definition emit_decl (T : sig_table) (E : sch_env) (d : kername * EAst.global_decl)
  : kername * bool * ExAst.global_decl :=
  let '(kn, d) := d in
  (kn, true,
   match d with
   | EAst.ConstantDecl cb => ExAst.ConstantDecl (emit_const E kn cb)
   | EAst.InductiveDecl mib => ExAst.InductiveDecl (emit_mib T kn mib)
   end).

(** The forward map. *)
Definition infer (Σ : EAst.global_context) : result' ExAst.global_env :=
  let '(T, cnt) := init_sigs Σ 0 in
  '(T1, E1, _) <- infer_go Σ T {| st_cnt := cnt; st_s := []; st_pend := []; st_inst := []; st_glob := []; st_taken := [] |};;
  Ok (map (emit_decl T1 E1) Σ).

(** ** The section lemma and its supporting inversions *)

Lemma trans_emit_const E kn (cb : EAst.constant_body) :
  ExAst.trans_cst (emit_const E kn cb) = cb.
Proof. destruct cb; reflexivity. Qed.

Lemma trans_ctors_emit params ctors g k :
  ExAst.trans_ctors (mapi_rec (fun c cb => emit_ctor params cb (g c)) ctors k) = ctors.
Proof.
  unfold ExAst.trans_ctors. revert k.
  induction ctors as [|[nm na] cs IH]; intros k; cbn; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma trans_projs_emit {A} (g : nat -> A) projs k :
  map (Basics.compose EAst.mkProjection fst)
      (mapi_rec (fun j p => (p.(EAst.proj_name), g j)) projs k) = projs.
Proof.
  revert k. induction projs as [|[nm] ps IH]; intros k; cbn; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma trans_emit_oib_aux params ctors (oib : EAst.one_inductive_body) :
  ExAst.trans_oib (emit_oib_aux params ctors oib) = oib.
Proof.
  destruct oib as [nm prop kelim cs projs].
  unfold ExAst.trans_oib, emit_oib_aux, mapi; cbn.
  rewrite trans_ctors_emit.
  rewrite (trans_projs_emit (fun j => emit_field params
             (match nth_error (match nth_error ctors 0 with Some fs => fs | None => [] end) j with
              | Some f => f | None => None end))).
  reflexivity.
Qed.

Lemma trans_emit_oib T kn i (oib : EAst.one_inductive_body) :
  ExAst.trans_oib (emit_oib T kn i oib) = oib.
Proof.
  unfold emit_oib. destruct (sig_lookup T kn); apply trans_emit_oib_aux.
Qed.

Lemma trans_emit_mib T kn (mib : EAst.mutual_inductive_body) :
  ExAst.trans_mib (emit_mib T kn mib) = mib.
Proof.
  destruct mib as [fin npars bodies].
  unfold ExAst.trans_mib, emit_mib; cbn.
  f_equal. unfold mapi. generalize 0 as k.
  induction bodies as [|o os IH]; intros k; cbn; [reflexivity|].
  rewrite trans_emit_oib. f_equal. apply IH.
Qed.

Lemma trans_emit_decl T E d :
  ExAst.trans_global_decl (snd (emit_decl T E d)) = snd d
  /\ fst (fst (emit_decl T E d)) = fst d.
Proof.
  destruct d as [kn [cb|mib]]; cbn; split; try reflexivity.
  - now rewrite trans_emit_const.
  - now rewrite trans_emit_mib.
Qed.

Lemma trans_env_emit T E Σ : ExAst.trans_env (map (emit_decl T E) Σ) = Σ.
Proof.
  induction Σ as [|[kn d] Σ IH]; [reflexivity|].
  unfold ExAst.trans_env in *; cbn. rewrite IH.
  destruct d as [cb|mib]; cbn; [now rewrite trans_emit_const|now rewrite trans_emit_mib].
Qed.

(** *** Main theorem: on success, [infer] is a section of [trans_env]. *)
Theorem infer_section (Σ : EAst.global_context) (Σ' : ExAst.global_env) :
  infer Σ = Ok Σ' -> ExAst.trans_env Σ' = Σ.
Proof.
  unfold infer. destruct (init_sigs Σ 0) as [T cnt].
  destruct (infer_go Σ T _) as [[[T1 E1] S1]|e]; cbn; intros H; [|discriminate].
  injection H as <-. apply trans_env_emit.
Qed.

(** ** Structural facts *)

(** Kernames and their order are preserved exactly. *)
Lemma infer_kernames (Σ : EAst.global_context) (Σ' : ExAst.global_env) :
  infer Σ = Ok Σ' -> map (fun '(kn, _, _) => kn) Σ' = map fst Σ.
Proof.
  unfold infer. destruct (init_sigs Σ 0) as [T cnt].
  destruct (infer_go Σ T _) as [[[T1 E1] S1]|e]; cbn; intros H; [|discriminate].
  injection H as <-. rewrite map_map.
  apply map_ext. intros [kn [cb|mib]]; reflexivity.
Qed.

(** Every emitted declaration carries [has_deps = true]. *)
Lemma infer_has_deps (Σ : EAst.global_context) (Σ' : ExAst.global_env) :
  infer Σ = Ok Σ' -> Forall (fun '(_, b, _) => b = true) Σ'.
Proof.
  unfold infer. destruct (init_sigs Σ 0) as [T cnt].
  destruct (infer_go Σ T _) as [[[T1 E1] S1]|e]; cbn; intros H; [|discriminate].
  injection H as <-. apply Forall_map, Forall_forall.
  intros [kn [cb|mib]] _; reflexivity.
Qed.

Print Assumptions infer_section.
Print Assumptions infer_kernames.
Print Assumptions infer_has_deps.
