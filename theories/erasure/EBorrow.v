(** * Borrow inference for reference-counted backends

    A parameter is borrowed when the callee never consumes it: the caller keeps
    ownership, and the callee neither increments nor decrements its count.
    Koka ([^x]) and Lean ([@&]) accept such annotations; a reference-counted
    Rust printer can pass [&T].  The annotation never changes the meaning of
    the program: Koka inserts the count operations a consumed borrowed
    parameter needs.  It changes their number, and so the running time.

    The analysis is the one of Ullrich and de Moura ("Counting immutable
    beans", IFL 2019), on lambda-box terms.  Every parameter starts borrowed
    and becomes owned, for good, when

    - it is consumed: it occurs anywhere but as a match scrutinee or as an
      argument at a borrowed position of a known function (returned, stored in
      a constructor, passed to an unknown function or an owned position,
      captured by a closure or a local fixpoint, bound by a let);
    - it is matched and a branch allocates a constructor that could reuse its
      cell ([reuse]; Perceus reuses a cell for a constructor of the same size);
    - a tail call to a function of its own group passes, at its position, a
      value the caller owns: the caller would release that value after the
      call, which is then no longer a tail call.

    The functions are given by the backend, which decides what is a function
    ([fn_def]): its parameters, its body under them, and what the variables
    beyond the parameters denote.  [check] tests the first condition for a
    table of modes; [check_sound] states what it guarantees. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst EAstUtils.
Import ListNotations.

Local Open Scope bs_scope.

Definition fid := string.

(** What a de Bruijn variable denotes in the body of the function analysed. *)
Inductive var_kind :=
| VParam (j : nat)          (* parameter [j] *)
| VField (j : nat)          (* bound by a match on parameter [j], or on such a variable *)
| VCapt (j : nat)           (* parameter [j] under a lambda or a local fixpoint *)
| VFun (f : fid) (ar : nat) (* a known function of arity [ar] *)
| VOther.

Inductive event := Consume (j : nat) | TailOwn (f : fid) (j : nat).

(** [modes]: per function, per parameter, [true] when borrowed. *)
Definition modes := list (fid * list bool).

Definition borrowed (ms : modes) (f : fid) (j : nat) : bool :=
  match find (fun p => String.eqb (fst p) f) ms with
  | Some (_, bs) => nth j bs false
  | None => false
  end.

Record fn_def := {
  fd_id : fid;
  fd_arity : nat;
  fd_body : term;               (* under the [fd_arity] parameters *)
  fd_ctx : list var_kind;       (* the variables beyond the parameters, innermost first *)
  fd_group : list fid           (* the functions a tail call keeps a tail call to *)
}.

Section Analysis.
  (** Constants called as known functions, with their arity. *)
  Context (const_fn : kername -> option (fid * nat)).
  (** [reuse k b]: a branch [b] binding [k] fields allocates a constructor that
      may reuse the matched cell. *)
  Context (reuse : nat -> term -> bool).

  Definition known (Γ : list var_kind) (h : term) : option (fid * nat) :=
    match h with
    | tRel n => match nth_error Γ n with Some (VFun f ar) => Some (f, ar) | _ => None end
    | tConst kn => const_fn kn
    | _ => None
    end.

  (** A variable that may be passed to a borrowed position without a count
      operation. *)
  Definition borrowable (Γ : list var_kind) (a : term) : bool :=
    match a with
    | tRel n => match nth_error Γ n with Some (VParam _) | Some (VField _) => true | _ => false end
    | _ => false
    end.

  (** A variable that the caller does not own. *)
  Definition caller_borrows (ms : modes) (self : fid) (Γ : list var_kind) (a : term) : bool :=
    match a with
    | tRel n =>
      match nth_error Γ n with
      | Some (VParam p) | Some (VField p) => borrowed ms self p
      | _ => false
      end
    | _ => false
    end.

  Definition capture (k : var_kind) : var_kind :=
    match k with
    | VParam j => VCapt j
    | VField _ => VOther
    | k => k
    end.

  Definition tail_events (ms : modes) (grp : list fid) (self : fid) (Γ : list var_kind)
    (h : term) (args : list term) : list event :=
    match known Γ h with
    | Some (g, ar) =>
      if existsb (String.eqb g) grp then
        List.concat (List.map (fun '(j, a) =>
          if andb (Nat.ltb j ar) (andb (borrowed ms g j) (negb (caller_borrows ms self Γ a)))
          then [TailOwn g j] else [])
          (combine (seq 0 (List.length args)) args))
      else []
    | None => []
    end.

  Definition all_params (Γ : list var_kind) : list event :=
    List.concat (List.map (fun k => match k with VParam j | VCapt j => [Consume j] | _ => [] end) Γ).

  Section Uses.
    Context (ms : modes) (grp : list fid) (self : fid).

    (** The events of [t]: [tail] when [t] is in tail position, [head] when [t]
        is the function part of an application. *)
    Fixpoint uses (Γ : list var_kind) (tail head : bool) (t : term) {struct t} : list event :=
      match t with
      | tRel n =>
        match nth_error Γ n with
        | Some (VParam j) | Some (VCapt j) => [Consume j]
        | _ => []
        end
      | tApp f a =>
        let '(h, args) := decompose_app (tApp f a) in
        let pos := List.length args - 1 in
        let ea :=
          match known Γ h with
          | Some (g, ar) =>
            if andb (Nat.ltb pos ar) (andb (borrowed ms g pos) (borrowable Γ a)) then []
            else uses Γ false false a
          | None => uses Γ false false a
          end in
        let et := if andb tail (negb head) then tail_events ms grp self Γ h args else [] in
        List.app ea (List.app et (uses Γ false true f))
      | tLambda _ b => uses (VOther :: List.map capture Γ) false false b
      | tLetIn _ v b => List.app (uses Γ false false v) (uses (VOther :: Γ) tail false b)
      | tCase _ d brs =>
        let '(ed, k, ev_reuse) :=
          match d with
          | tRel n =>
            match nth_error Γ n with
            | Some (VParam j) =>
              ([], VField j,
               if existsb (fun br => reuse (List.length (fst br)) (snd br)) brs then [Consume j] else [])
            | Some (VField j) => ([], VField j, [])
            | _ => (uses Γ false false d, VOther, [])
            end
          | _ => (uses Γ false false d, VOther, [])
          end in
        List.app ed (List.app ev_reuse
          (List.concat (List.map (fun br => uses (List.app (repeat k (List.length (fst br))) Γ) tail false (snd br)) brs)))
      | tFix mfix _ | tCoFix mfix _ =>
        List.concat (List.map (fun d => uses (List.app (repeat VOther (List.length mfix)) (List.map capture Γ)) false false (dbody d)) mfix)
      | tConstruct _ _ args => List.concat (List.map (uses Γ false false) args)
      | tEvar _ l => List.concat (List.map (uses Γ false false) l)
      | tProj _ c => uses Γ false false c
      | tLazy c | tForce c => uses Γ false false c
      | tPrim _ => all_params Γ
      | tBox | tVar _ | tConst _ => []
      end.
  End Uses.

  Definition param_ctx (n : nat) : list var_kind := List.map VParam (List.rev (seq 0 n)).

  Definition fd_events (ms : modes) (fd : fn_def) : list event :=
    uses ms (fd_group fd) (fd_id fd) (List.app (param_ctx (fd_arity fd)) (fd_ctx fd)) true false (fd_body fd).

  Definition is_consume (j : nat) (e : event) : bool :=
    match e with Consume i => Nat.eqb i j | _ => false end.

  Definition is_tailown (f : fid) (j : nat) (e : event) : bool :=
    match e with TailOwn g i => andb (String.eqb g f) (Nat.eqb i j) | _ => false end.

  (** One round: a parameter stays borrowed unless an event makes it owned. *)
  Definition step (fds : list fn_def) (ms : modes) : modes :=
    let evs := List.map (fun fd => (fd, fd_events ms fd)) fds in
    let tails := List.concat (List.map snd evs) in
    List.map (fun '(fd, es) =>
      (fd_id fd, List.map (fun j =>
         andb (borrowed ms (fd_id fd) j)
              (negb (orb (existsb (is_consume j) es) (existsb (is_tailown (fd_id fd) j) tails))))
         (seq 0 (fd_arity fd)))) evs.

  Definition init (fds : list fn_def) : modes :=
    List.map (fun fd => (fd_id fd, repeat true (fd_arity fd))) fds.

  Fixpoint iterate (fuel : nat) (fds : list fn_def) (ms : modes) : modes :=
    match fuel with
    | 0 => ms
    | S k => let ms' := step fds ms in iterate k fds ms'
    end.

  (** Modes only move from borrowed to owned, so as many rounds as there are
      parameters, plus one, reach the fixed point. *)
  Definition infer_modes (fds : list fn_def) : modes :=
    iterate (S (List.fold_left (fun n fd => n + fd_arity fd) fds 0)) fds (init fds).

  (** No borrowed parameter is consumed, for the modes [ms] themselves. *)
  Definition check (fds : list fn_def) (ms : modes) : bool :=
    forallb (fun fd =>
      let es := fd_events ms fd in
      forallb (fun j => implb (borrowed ms (fd_id fd) j) (negb (existsb (is_consume j) es)))
              (seq 0 (fd_arity fd))) fds.

  (** The modes a backend uses: the inferred ones if they pass [check], and
      every parameter owned otherwise. *)
  Definition borrow_modes (fds : list fn_def) : modes :=
    let ms := infer_modes fds in
    if check fds ms then ms else List.map (fun fd => (fd_id fd, repeat false (fd_arity fd))) fds.

  Lemma borrowed_owned_all fds f j :
    borrowed (List.map (fun fd => (fd_id fd, repeat false (fd_arity fd))) fds) f j = false.
  Proof.
    unfold borrowed.
    destruct (find _ _) as [[g bs]|] eqn:E; [|reflexivity].
    apply find_some in E as [Hin _].
    apply in_map_iff in Hin as [fd [Heq _]]. inversion Heq; subst.
    apply nth_repeat.
  Qed.

  (** [check_sound]: with the modes [borrow_modes] returns, a parameter that is
      borrowed is never consumed by the body of its function. *)
  Theorem check_sound fds fd j :
    In fd fds -> borrowed (borrow_modes fds) (fd_id fd) j = true ->
    j < fd_arity fd ->
    existsb (is_consume j) (fd_events (borrow_modes fds) fd) = false.
  Proof.
    intros Hin Hb Hj. unfold borrow_modes in *.
    destruct (check fds (infer_modes fds)) eqn:C.
    - unfold check in C. rewrite forallb_forall in C. specialize (C fd Hin). cbv beta in C.
      rewrite forallb_forall in C. specialize (C j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l _) Hj))).
      rewrite Hb in C. simpl in C. apply negb_true_iff in C. exact C.
    - rewrite borrowed_owned_all in Hb. discriminate.
  Qed.
End Analysis.
