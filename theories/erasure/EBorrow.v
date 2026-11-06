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
    table of modes.  [BO] says in rules what "not consumed" means, and
    [borrow_modes_spec] proves that every parameter [borrow_modes] marks
    borrowed satisfies it. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst EAstUtils EInduction.
From MetaRocq.Utils Require Import All_Forall.
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

  (** A match on [d]: whether [d]'s own events count, the kind of the variables
      the branches bind, and the event of a cell the branches may reuse. *)
  Definition case_scrut (Γ : list var_kind) (d : term) (brs : list (list name * term))
    : bool * var_kind * list event :=
    match d with
    | tRel n =>
      match nth_error Γ n with
      | Some (VParam j) =>
        (false, VField j,
         if existsb (fun br => reuse (List.length (fst br)) (snd br)) brs then [Consume j] else [])
      | Some (VField j) => (false, VField j, [])
      | _ => (true, VOther, [])
      end
    | _ => (true, VOther, [])
    end.

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
        let '(own, k, ev_reuse) := case_scrut Γ d brs in
        List.app (if own then uses Γ false false d else []) (List.app ev_reuse
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

  (** ** What "not consumed" means

      [BO ms j Γ t]: in [t], parameter [j] occurs only as the scrutinee of a
      match whose branches do not reuse its cell, or as an argument at a
      borrowed position of a known function.  Under a closure or a local
      fixpoint it does not occur at all.  Variables bound by a match on the
      parameter are its fields, and using those does not consume it. *)
  Section Spec.
    Context (ms : modes) (j : nat).

    Definition at_borrowed_pos (Γ : list var_kind) (f a : term) : bool :=
      let '(h, args) := decompose_app (tApp f a) in
      match known Γ h with
      | Some (g, ar) =>
        let pos := List.length args - 1 in
        andb (Nat.ltb pos ar) (andb (borrowed ms g pos) (borrowable Γ a))
      | None => false
      end.

    Definition not_param (Γ : list var_kind) (n : nat) : Prop :=
      nth_error Γ n <> Some (VParam j) /\ nth_error Γ n <> Some (VCapt j).

    (** The kind of the variables a match on [d] binds, when [d] is a parameter
        or one of its fields. *)
    Definition scrut_kind (Γ : list var_kind) (d : term) : option var_kind :=
      match d with
      | tRel n =>
        match nth_error Γ n with
        | Some (VParam i) | Some (VField i) => Some (VField i)
        | _ => None
        end
      | _ => None
      end.

    Definition no_reuse_of_param (Γ : list var_kind) (d : term) (brs : list (list name * term)) : Prop :=
      match d with
      | tRel n =>
        nth_error Γ n = Some (VParam j) ->
        existsb (fun br => reuse (List.length (fst br)) (snd br)) brs = false
      | _ => True
      end.

    Inductive BO : list var_kind -> term -> Prop :=
    | BO_box Γ : BO Γ tBox
    | BO_var Γ i : BO Γ (tVar i)
    | BO_const Γ k : BO Γ (tConst k)
    | BO_rel Γ n : not_param Γ n -> BO Γ (tRel n)
    | BO_app Γ f a :
        BO Γ f -> (at_borrowed_pos Γ f a = true \/ BO Γ a) -> BO Γ (tApp f a)
    | BO_lam Γ na b : BO (VOther :: List.map capture Γ) b -> BO Γ (tLambda na b)
    | BO_let Γ na v b : BO Γ v -> BO (VOther :: Γ) b -> BO Γ (tLetIn na v b)
    | BO_case_var Γ ci d brs k :
        scrut_kind Γ d = Some k ->
        no_reuse_of_param Γ d brs ->
        Forall (fun br => BO (List.app (repeat k (List.length (fst br))) Γ) (snd br)) brs ->
        BO Γ (tCase ci d brs)
    | BO_case Γ ci d brs :
        scrut_kind Γ d = None ->
        BO Γ d ->
        Forall (fun br => BO (List.app (repeat VOther (List.length (fst br))) Γ) (snd br)) brs ->
        BO Γ (tCase ci d brs)
    | BO_fix Γ mfix i :
        Forall (fun d => BO (List.app (repeat VOther (List.length mfix)) (List.map capture Γ)) (dbody d)) mfix ->
        BO Γ (tFix mfix i)
    | BO_cofix Γ mfix i :
        Forall (fun d => BO (List.app (repeat VOther (List.length mfix)) (List.map capture Γ)) (dbody d)) mfix ->
        BO Γ (tCoFix mfix i)
    | BO_construct Γ ind c args : Forall (BO Γ) args -> BO Γ (tConstruct ind c args)
    | BO_evar Γ e l : Forall (BO Γ) l -> BO Γ (tEvar e l)
    | BO_proj Γ pr c : BO Γ c -> BO Γ (tProj pr c)
    | BO_lazy Γ c : BO Γ c -> BO Γ (tLazy c)
    | BO_force Γ c : BO Γ c -> BO Γ (tForce c)
    | BO_prim Γ p : existsb (is_consume j) (all_params Γ) = false -> BO Γ (tPrim p).

    Lemma existsb_concat_map {A} (f : event -> bool) (g : A -> list event) (l : list A) :
      existsb f (List.concat (List.map g l)) = false ->
      forall x, In x l -> existsb f (g x) = false.
    Proof.
      induction l as [|y l IH]; simpl; intros H x Hx; [contradiction|].
      rewrite existsb_app in H. apply orb_false_iff in H as [H1 H2].
      destruct Hx as [<-|Hx]; [exact H1|]. exact (IH H2 x Hx).
    Qed.

    Lemma tail_events_no_consume grp self Γ h args :
      existsb (is_consume j) (tail_events ms grp self Γ h args) = false.
    Proof.
      unfold tail_events. destruct (known Γ h) as [[g ar]|]; [|reflexivity].
      destruct (existsb (String.eqb g) grp); [|reflexivity].
      generalize (combine (seq 0 (List.length args)) args) as l.
      induction l as [|[i a] l IH]; [reflexivity|]. simpl.
      rewrite existsb_app, IH, orb_false_r.
      match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
    Qed.

    Theorem no_consume_BO grp self t : forall Γ tl hd,
      existsb (is_consume j) (uses ms grp self Γ tl hd t) = false -> BO Γ t.
    Proof.
      induction t using term_forall_list_ind; intros Γ tl hd H; simpl in H.
      - constructor.
      - constructor. unfold not_param.
        destruct (nth_error Γ n) as [[i|i|i|f ar|]|] eqn:E;
          simpl in H; split; try discriminate; intro Heq; inversion Heq; subst;
          simpl in H; rewrite Nat.eqb_refl in H; discriminate.
      - constructor.
      - constructor. apply All_Forall in X. rewrite Forall_forall in *. intros a Ha.
        eapply (X a Ha). exact (existsb_concat_map _ (uses ms grp self Γ false false) _ H a Ha).
      - constructor. eapply IHt. exact H.
      - rewrite existsb_app in H. apply orb_false_iff in H as [H1 H2].
        constructor; [eapply IHt1; exact H1 | eapply IHt2; exact H2].
      - assert (Hdec : decompose_app (tApp t1 t2) = decompose_app_rec t1 [t2]) by reflexivity.
        try unfold decompose_app in H. cbn [decompose_app_rec] in H.
        destruct (decompose_app_rec t1 [t2]) as [h args] eqn:Hd.
        simpl in H. rewrite !existsb_app in H. apply orb_false_iff in H as [Ha H].
        apply orb_false_iff in H as [_ Hf].
        constructor; [eapply IHt1; exact Hf|].
        unfold at_borrowed_pos. rewrite Hdec.
        destruct (known Γ h) as [[g ar]|]; cbv zeta in *.
        + match goal with |- (?c = true) \/ _ => destruct c eqn:C end;
            [left; reflexivity | right; eapply IHt2; exact Ha].
        + right. eapply IHt2. exact Ha.
      - constructor.
      - constructor. apply All_Forall in X. rewrite Forall_forall in *. intros a Ha.
        eapply (X a Ha). exact (existsb_concat_map _ (uses ms grp self Γ false false) _ H a Ha).
      - (* a match *)
        destruct (case_scrut Γ t l) as [[own k] ev] eqn:Cs.
        simpl in H. rewrite !existsb_app in H. apply orb_false_iff in H as [H0 H].
        apply orb_false_iff in H as [Hev Hbrs].
        assert (Hall : Forall (fun br => BO (List.app (repeat k (List.length (fst br))) Γ) (snd br)) l).
        { apply All_Forall in X. rewrite Forall_forall in *. intros br Hbr.
          eapply (X br Hbr) with (tl := tl) (hd := false).
          exact (existsb_concat_map _ (fun br => uses ms grp self (List.app (repeat k (List.length (fst br))) Γ) tl false (snd br)) _ Hbrs br Hbr). }
        destruct own.
        + assert (Hk : scrut_kind Γ t = None /\ k = VOther).
          { clear -Cs. unfold case_scrut, scrut_kind in *.
            destruct t; inversion Cs; subst; try (split; reflexivity).
            destruct (nth_error Γ n) as [[i|i|i|f ar|]|]; inversion Cs; subst; split; reflexivity. }
          destruct Hk as [Hs ->]. eapply BO_case; [exact Hs| eapply IHt; exact H0 | exact Hall].
        + assert (Hk : scrut_kind Γ t = Some k /\ no_reuse_of_param Γ t l).
          { clear -Cs Hev. unfold case_scrut, scrut_kind, no_reuse_of_param in *.
            destruct t; try (inversion Cs; fail).
            destruct (nth_error Γ n) as [[i|i|i|f ar|]|] eqn:E; inversion Cs; subst.
            - split; [reflexivity|]. intro Heq.
              assert (i = j) as -> by congruence.
              destruct (existsb (fun br => reuse (List.length (fst br)) (snd br)) l) eqn:Ex; [|reflexivity].
              exfalso. simpl in Hev. rewrite Nat.eqb_refl in Hev. discriminate.
            - split; [reflexivity|]. intro Heq. congruence. }
          destruct Hk as [Hs Hr]. eapply BO_case_var; [exact Hs|exact Hr|exact Hall].
      - constructor. eapply IHt. exact H.
      - constructor. apply All_Forall in X. rewrite Forall_forall in *. intros d Hd.
        eapply (X d Hd). exact (existsb_concat_map _ (fun d => uses ms grp self (List.app (repeat VOther (List.length m)) (List.map capture Γ)) false false (dbody d)) _ H d Hd).
      - constructor. apply All_Forall in X. rewrite Forall_forall in *. intros d Hd.
        eapply (X d Hd). exact (existsb_concat_map _ (fun d => uses ms grp self (List.app (repeat VOther (List.length m)) (List.map capture Γ)) false false (dbody d)) _ H d Hd).
      - constructor. exact H.
      - constructor. eapply IHt. exact H.
      - constructor. eapply IHt. exact H.
    Qed.
  End Spec.

  (** A parameter that [borrow_modes] marks borrowed satisfies [BO] in the body
      of its function. *)
  Theorem borrow_modes_spec fds fd j :
    In fd fds -> borrowed (borrow_modes fds) (fd_id fd) j = true -> j < fd_arity fd ->
    BO (borrow_modes fds) j (List.app (param_ctx (fd_arity fd)) (fd_ctx fd)) (fd_body fd).
  Proof.
    intros Hin Hb Hj. eapply no_consume_BO. exact (check_sound fds fd j Hin Hb Hj).
  Qed.
End Analysis.
