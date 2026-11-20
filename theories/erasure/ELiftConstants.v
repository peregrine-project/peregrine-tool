(** * Lifting closed constructor values to shared global constants

    This middle-end pass hoists every maximal closed constructor value of a
    lambda-box program -- most importantly unary [nat] literals such as
    [S (S (... O))] -- into a fresh top-level constant, and replaces every
    occurrence of the value by a reference to that constant.  Structurally
    equal values share one constant, so a literal that appears in several
    constants is allocated once for the whole program.

    Motivation.  Lambda-box keeps literals as constructor chains, and backends
    that compile a constructor application to an allocation (the CertiRocq C
    backend, Wasm, Rust, CakeML, Lean) re-allocate such a chain every time the
    enclosing code runs: a function body containing the literal [1009] builds a
    1009-cell chain on every call, and a program whose data refers to such
    chains (for instance the suffixes returned by [sub]) ends up with as many
    copies of the chain as there were calls, which destroys locality.
    [ocamlopt] instead emits closed constructor values as static data.  A
    global constant is evaluated once (at initialisation, or emitted as static
    data) by every backend, so lifting the values restores sharing uniformly.

    ---------------------------------------------------------------------------
    ALGORITHM.

    A term is a closed constructor value ([cvalue_size t = Some n]) when it is
    [tBox] or a block constructor [tConstruct ind c args] all of whose
    arguments are closed constructor values; [n] counts its constructors.
    The pass only fires on values with at least [lift_threshold] (= 2)
    constructors: a bare nullary constructor or [tBox] is already as cheap as a
    reference to a global.

    For every declaration of the environment, from the deepest (last) to the
    shallowest (first), and finally for the main term:

      1. [collect_values] returns the maximal closed constructor values of size
         at least [lift_threshold] occurring in the body (a value is never
         descended into, so only maximal values are collected);
      2. each value that is not yet in the table of lifted values gets a fresh
         kername [lift_kn i] (module path [lift_mp], index [i] = current table
         size) and a new constant declaration whose body is the value.  The new
         declarations are inserted directly *below* the declaration that uses
         them, i.e. after it in the list, so they are in scope for it and for
         every shallower declaration, and the inductive types they mention are
         in scope for them (they were in scope for the declaration itself);
      3. [replace] rewrites the body, substituting [tConst kn] for every
         maximal value registered in the table under [kn].

    A constant whose entire body is a closed constructor value of size at least
    [lift_threshold] is lifted like any other occurrence: its body becomes a
    reference to the lifted constant, which it shares with the other
    occurrences of the value.  The value is not registered under the
    constant's own name, because the constant may be remapped to a foreign
    value.  The main term is treated like a
    body, except that it is left alone when it is itself a value.

    The pass is the identity when the environment already contains a kername
    under [lift_mp] (so freshness of the generated names is guaranteed by a
    single syntactic check), or when the environment flags forbid [tConst].
    Constructors must be represented as blocks for the pass to find anything;
    it runs in [extra_unsafe_transforms] (erasure/Transforms.v), after
    [betared], dead-argument elimination, instance specialisation and CSE,
    and before [implement_box], in the constructors-as-blocks regime.  It is
    off by default in every backend ([lift_constants] field of
    [erasure_phases], flag [--lift-constants]).

    The typed pipeline (Rust, Elm) does not run the pass: a typed global
    environment ([ExAst]) requires a type for every constant, and computing the
    type of an arbitrary closed constructor value ([cons 1 nil : list nat])
    would need type inference over the constructor's type scheme, which the
    typed pipeline does not provide at this point.

    ---------------------------------------------------------------------------
    VERIFICATION STATUS.

    The pass is verified, without axioms: [lift_program_wf] (the output
    program is wellformed) and [lift_program_pres] (if the input program
    evaluates to [v], the output program evaluates to some [v'] with
    [lift_rel Σ' v v'], [Σ'] the output environment) discharge the two
    obligations of [lift_constants_transformation].  [lift_rel Σ'] relates a
    term to the same term in which some liftable closed constructor values
    have been replaced by [tConst kn], [kn] being declared in [Σ'] with that
    value as its body.  The proof goes in three steps.
    - Simulation ([lift_rel_simulation]): for any environments [Σ], [Σ'] with
      the same inductives and whose constant bodies are [lift_rel Σ']-related,
      [eval Σ t v] and [lift_rel Σ' t t'] give [eval Σ' t' v'] with
      [lift_rel Σ' v v'].  The new case, a value replaced by [tConst kn],
      evaluates by [eval_delta] to the body; the other cases are congruences,
      as [lift_rel] commutes with [csubst]/[substl] (the replaced values are
      closed) and the heads of evaluation results are never [tConst].
    - Invariants of [lift_env] ([lift_env_inv]): every table entry is declared
      with its value as body; the indices [≥ #|tbl|] are fresh; the
      inductives are unchanged; each original constant body is related to
      its image; the output environment is wellformed.  This needs that no
      name of the input lives under [lift_mp], which [lift_enabled] checks.
    - Wellformedness transfer along [lift_rel] ([wellformed_lift_rel]).
    The pass does not satisfy the [TransformExt] obligations (the generated
    names are numbered by table position, which an extension of the
    environment can change), and none is provided: the pipeline does not use
    them. *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
     ECSubst EReflect EGlobalEnv EProgram EWellformed EWcbvEval.
From MetaRocq.Erasure Require EBeta.

Import ListNotations.

(** Tunable parameter: minimal number of constructors in a lifted value. *)
Definition lift_threshold : nat := 2.

(** ** Names of the generated constants *)

Definition lift_mp : modpath := MPfile ["LiftConstants"%bs; "Peregrine"%bs].

Definition lift_kn (i : nat) : kername :=
  (lift_mp, ("lifted_constant_" ++ string_of_nat i)%bs).

Definition is_lift_kn (kn : kername) : bool := eqb kn (lift_mp, kn.2).

(** ** Closed constructor values *)

(** [cvalue_size t = Some n] iff [t] is a closed constructor value made of
    [n] constructors (boxes count 0). *)
Fixpoint cvalue_size (t : term) : option nat :=
  match t with
  | tBox => Some 0
  | tConstruct ind c args =>
      let fix go (l : list term) : option nat :=
        match l with
        | [] => Some 0
        | a :: l =>
            match cvalue_size a, go l with
            | Some n, Some m => Some (n + m)
            | _, _ => None
            end
        end in
      match go args with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.

Definition cvalue_sizes (l : list term) : option nat :=
  fold_right (fun a acc =>
      match cvalue_size a, acc with
      | Some n, Some m => Some (n + m)
      | _, _ => None
      end) (Some 0) l.

Lemma cvalue_size_construct ind c args :
  cvalue_size (tConstruct ind c args) = option_map S (cvalue_sizes args).
Proof.
  cbn. induction args as [|a l IH]; cbn; auto.
  all: destruct (cvalue_size a); auto.
  all: destruct (cvalue_sizes l) eqn:E; auto; cbn in IH; rewrite <- IH; auto.
Qed.

Definition is_cvalue (t : term) : bool := isSome (cvalue_size t).

(** Should this value be lifted? *)
Definition liftable (t : term) : bool :=
  match cvalue_size t with
  | Some n => lift_threshold <=? n
  | None => false
  end.

(** ** Collecting maximal liftable values *)

Fixpoint collect_values (t : term) : list term :=
  if liftable t then [t] else
  match t with
  | tEvar _ ts => flat_map collect_values ts
  | tLambda _ b => collect_values b
  | tLetIn _ v b => collect_values v ++ collect_values b
  | tApp f a => collect_values f ++ collect_values a
  | tCase _ d brs => collect_values d ++ flat_map (fun br => collect_values (snd br)) brs
  | tProj _ u => collect_values u
  | tFix mf _ => flat_map (fun d => collect_values (dbody d)) mf
  | tCoFix mf _ => flat_map (fun d => collect_values (dbody d)) mf
  | tConstruct _ _ args => flat_map collect_values args
  | tLazy u => collect_values u
  | tForce u => collect_values u
  | _ => []
  end.

(** ** The table of lifted values *)

Definition table := list (term × kername).

(** Structural equality of closed constructor values, the only terms that the
    table holds or is queried with ([false] on any other term).  Unlike the
    [eqb] of [ReflectEq term], whose decision procedure goes through an opaque
    proof, it computes inside Rocq, so that the checks at the end of this file
    run by [vm_compute]. *)
Fixpoint cvalue_eqb (t u : term) : bool :=
  match t, u with
  | tBox, tBox => true
  | tConstruct ind c args, tConstruct ind' c' args' =>
      eqb ind ind' && Nat.eqb c c' &&
      (fix go (l l' : list term) : bool :=
         match l, l' with
         | [], [] => true
         | a :: l, a' :: l' => cvalue_eqb a a' && go l l'
         | _, _ => false
         end) args args'
  | _, _ => false
  end.

Definition lookup_table (tbl : table) (v : term) : option kername :=
  match find (fun p => cvalue_eqb p.1 v) tbl with
  | Some p => Some p.2
  | None => None
  end.

Definition mem_table (tbl : table) (v : term) : bool :=
  isSome (lookup_table tbl v).

(** Values of [l] not yet in [tbl], without duplicates, in order of first
    occurrence. *)
Fixpoint new_values (tbl : table) (l : list term) : list term :=
  match l with
  | [] => []
  | v :: l =>
      if mem_table tbl v then new_values tbl l
      else v :: new_values ((v, lift_kn #|tbl|) :: tbl) l
  end.

(** Register [vs] (pairwise distinct, not in [tbl]) under fresh names. *)
Fixpoint register (tbl : table) (vs : list term) : table :=
  match vs with
  | [] => tbl
  | v :: vs => register ((v, lift_kn #|tbl|) :: tbl) vs
  end.

Definition new_decls (tbl : table) (vs : list term) : list (kername × global_decl) :=
  mapi (fun i v => (lift_kn (#|tbl| + i), ConstantDecl {| cst_body := Some v |})) vs.

(** ** Replacing the values by references to the lifted constants *)

Fixpoint replace (tbl : table) (t : term) : term :=
  if liftable t then
    match lookup_table tbl t with
    | Some kn => tConst kn
    | None => t
    end
  else
  match t with
  | tPrim _ => t  (* [collect_values] does not look into primitive values *)
  | _ => EBeta.map_subterms (replace tbl) t
  end.

(** ** Per-declaration processing *)

(** Process a constant body [t] (or the main term) against [tbl]: returns the
    rewritten term, the new declarations to insert below it, and the extended
    table.  A body that is itself a value is left alone (nothing is lifted
    out of it). *)
Definition lift_body (tbl : table) (t : term)
  : term * list (kername × global_decl) * table :=
  if is_cvalue t then (t, [], tbl)
  else
    let vs := new_values tbl (collect_values t) in
    let tbl' := register tbl vs in
    (replace tbl' t, new_decls tbl vs, tbl').

Definition lift_decl (tbl : table) (kn : kername) (d : global_decl)
  : global_decl * list (kername × global_decl) * table :=
  match d with
  | ConstantDecl {| cst_body := Some t |} =>
      if liftable t then
        (* The whole body is a liftable value: it becomes a reference to the
           shared lifted constant, which is created if needed.  The value is
           not registered under [kn] itself: [kn] may be remapped to a foreign
           value, which the other occurrences must not refer to. *)
        match lookup_table tbl t with
        | Some kn' => (ConstantDecl {| cst_body := Some (tConst kn') |}, [], tbl)
        | None =>
            (ConstantDecl {| cst_body := Some (tConst (lift_kn #|tbl|)) |},
             new_decls tbl [t], (t, lift_kn #|tbl|) :: tbl)
        end
      else
        let '(t', news, tbl') := lift_body tbl t in
        (ConstantDecl {| cst_body := Some t' |}, news, tbl')
  | _ => (d, [], tbl)
  end.

(** Process the environment from the deepest declaration up.  The inserted
    declarations follow (are deeper than) the declaration that uses them. *)
Fixpoint lift_env (Σ : global_declarations) : global_declarations × table :=
  match Σ with
  | [] => ([], [])
  | (kn, d) :: Σ =>
      let '(Σ', tbl) := lift_env Σ in
      let '(d', news, tbl') := lift_decl tbl kn d in
      ((kn, d') :: news ++ Σ', tbl')
  end.

Definition lift_enabled (efl : EEnvFlags) (Σ : global_declarations) : bool :=
  has_tConst && has_tConstruct && negb (existsb (fun d => is_lift_kn d.1) Σ).

Definition lift_program (efl : EEnvFlags) (p : program) : program :=
  if lift_enabled efl p.1 then
    let '(Σ', tbl) := lift_env p.1 in
    let '(t', news, _) := lift_body tbl p.2 in
    (news ++ Σ', t')
  else p.

(** * VERIFICATION *)

(** ** (1) Closed constructor values *)

Lemma cvalue_sizes_cons a l :
  cvalue_sizes (a :: l) =
  match cvalue_size a, cvalue_sizes l with
  | Some n, Some m => Some (n + m)
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma cvalue_sizes_All (P : term -> Type) args m :
  All (fun t => forall n, cvalue_size t = Some n -> P t) args ->
  cvalue_sizes args = Some m -> All P args.
Proof.
  intros X. revert m. induction X as [|a l Ha Hl IH]; intros m H; [constructor|].
  rewrite cvalue_sizes_cons in H.
  destruct (cvalue_size a) as [na|] eqn:Ea; [| discriminate].
  destruct (cvalue_sizes l) as [ml|] eqn:El; [| discriminate].
  constructor; eauto.
Qed.

Lemma cvalue_closed t n : cvalue_size t = Some n -> forall k, closedn k t.
Proof.
  revert n. induction t using EInduction.term_forall_list_ind; intros n0 H k;
    try (cbn in H; discriminate).
  - reflexivity.
  - rewrite cvalue_size_construct in H.
    destruct (cvalue_sizes args) as [m|] eqn:E; [| discriminate].
    cbn. apply All_forallb. eapply cvalue_sizes_All; [|exact E].
    eapply All_impl; [exact X|]. cbn. intros x Hx n' Hn'. eapply Hx; eauto.
Qed.

Lemma cvalue_lift t n i k : cvalue_size t = Some n -> lift i k t = t.
Proof.
  intros H. eapply ELiftSubst.lift_closed. eapply (cvalue_closed _ _ H).
Qed.

Lemma cvalue_csubst t n a k : cvalue_size t = Some n -> csubst a k t = t.
Proof.
  intros H. apply ECSubst.csubst_closed. eapply (cvalue_closed _ _ H).
Qed.

(** A closed constructor value of a wellformed block-constructor regime
    evaluates to itself.  *)
Lemma cvalue_eval_self {wfl : WcbvFlags} Σ t n :
  with_constructor_as_block = true ->
  (forall ind c args, cvalue_size (tConstruct ind c args) <> None ->
     ∑ mdecl idecl cdecl, (lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl))
       * (#|args| = cstr_arity mdecl cdecl)) ->
  cvalue_size t = Some n -> eval Σ t t.
Proof.
  intros Hb Hlook. revert n.
  induction t using EInduction.term_forall_list_ind; intros n0 H;
    try (cbn in H; discriminate).
  - eapply eval_atom. reflexivity.
  - destruct (Hlook i n args) as (mdecl & idecl & cdecl & Hl & Ha).
    { rewrite H. discriminate. }
    rewrite cvalue_size_construct in H.
    destruct (cvalue_sizes args) as [m|] eqn:E; [| discriminate].
    assert (X' : All (fun a => eval Σ a a) args).
    { eapply cvalue_sizes_All; [|exact E].
      eapply All_impl; [exact X|]. cbn. intros x Hx n' Hn'. eapply Hx; eauto. }
    eapply eval_construct_block; eauto.
    clear -X'. induction X'; constructor; auto.
Qed.

(** Unfolding a constant whose body is a closed constructor value yields the
    value itself. *)
Lemma eval_tConst_cvalue {wfl : WcbvFlags} Σ kn t n :
  declared_constant Σ kn {| cst_body := Some t |} ->
  eval Σ t t ->
  cvalue_size t = Some n ->
  eval Σ (tConst kn) t.
Proof.
  intros Hd Hev _. eapply eval_delta; [exact Hd | reflexivity | exact Hev].
Qed.

(** ** (2) Environment lookups *)

Lemma lookup_env_app_fresh Σ1 Σ2 kn :
  Forall (fun d => d.1 <> kn) Σ1 ->
  lookup_env (Σ1 ++ Σ2) kn = lookup_env Σ2 kn.
Proof.
  induction 1 as [|[kn' d] Σ1 H1 _ IH]; [reflexivity|].
  cbn [app lookup_env fst]. destruct (eqb_spec kn kn') as [Heq|Hne].
  - exfalso. apply H1. cbn. congruence.
  - exact IH.
Qed.

Lemma new_decls_names tbl vs kn :
  is_lift_kn kn = false -> Forall (fun d => d.1 <> kn) (new_decls tbl vs).
Proof.
  intros Hkn. unfold new_decls. generalize #|tbl| as m. intros m.
  unfold mapi. generalize 0 as i.
  induction vs as [|v vs IH]; intros i; [constructor|].
  cbn [mapi_rec]. constructor; [|apply IH].
  intros Heq. cbn in Heq. subst kn.
  change (eqb (lift_kn (m + i)) (lift_kn (m + i)) = false) in Hkn.
  rewrite eqb_refl in Hkn. discriminate.
Qed.

Lemma lift_decl_news tbl kn d d' news tbl' kn' :
  lift_decl tbl kn d = (d', news, tbl') -> is_lift_kn kn' = false ->
  Forall (fun x => x.1 <> kn') news.
Proof.
  unfold lift_decl, lift_body. intros H Hkn'.
  destruct d as [[[t|]]|]; cbv beta iota in H;
    try (injection H as <- <- <-; constructor).
  destruct (liftable t).
  - destruct (lookup_table tbl t); cbv beta iota in H;
      injection H as <- <- <-; [constructor | now apply new_decls_names].
  - destruct (is_cvalue t); cbv beta iota in H; injection H as <- <- <-;
      [constructor | now apply new_decls_names].
Qed.

(** A lookup of a name that is not a generated name goes through the
    inserted declarations and finds the processed original declaration. *)
Lemma lookup_env_lift_env Σ kn :
  is_lift_kn kn = false ->
  match lookup_env Σ kn, lookup_env (lift_env Σ).1 kn with
  | None, None => True
  | Some d, Some d' => exists tbl news tbl', lift_decl tbl kn d = (d', news, tbl')
  | _, _ => False
  end.
Proof.
  intros Hkn. induction Σ as [|[kn' d] Σ IH]; [exact I|].
  cbn [lift_env].
  destruct (lift_env Σ) as [Σ' tbl] eqn:E.
  destruct (lift_decl tbl kn' d) as [[d' news] tbl'] eqn:E'.
  cbn [lookup_env fst snd]. destruct (eqb_spec kn kn') as [->|Hne].
  - eauto.
  - rewrite lookup_env_app_fresh; [exact IH | eapply lift_decl_news; eauto].
Qed.



(** ** (3) Auxiliary facts *)

From Stdlib Require Import DecimalNat.
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Lemma string_append_inj_l (p s s' : String.t) :
  String.append p s = String.append p s' -> s = s'.
Proof.
  induction p as [|b p IH]; cbn; [easy|].
  intros H. injection H as H. now apply IH.
Qed.

Lemma string_of_uint_inj u u' :
  MRString.string_of_uint u = MRString.string_of_uint u' -> u = u'.
Proof.
  induction u in u' |- *; destruct u'; cbn; intros H; try discriminate;
    try reflexivity; injection H as H; f_equal; auto.
Qed.

Lemma lift_kn_inj i j : lift_kn i = lift_kn j -> i = j.
Proof.
  unfold lift_kn. intros H. injection H as H.
  try apply string_append_inj_l in H.
  apply string_of_uint_inj in H.
  rewrite <- (Unsigned.of_to i), <- (Unsigned.of_to j). now f_equal.
Qed.

Lemma is_lift_kn_lift_kn i : is_lift_kn (lift_kn i) = true.
Proof. unfold is_lift_kn. cbn [snd lift_kn]. apply eqb_refl. Qed.

Lemma lift_kn_not_orig kn i : is_lift_kn kn = false -> kn <> lift_kn i.
Proof. intros H ->. now rewrite is_lift_kn_lift_kn in H. Qed.

Lemma lookup_env_cons kn' d Σ kn :
  lookup_env ((kn', d) :: Σ) kn = if eqb kn kn' then Some d else lookup_env Σ kn.
Proof. reflexivity. Qed.

Lemma fresh_global_lookup kn Σ : lookup_env Σ kn = None -> fresh_global kn Σ.
Proof.
  induction Σ as [|[kn' d] Σ IH]; [constructor|].
  cbn [lookup_env fst snd]. destruct (eqb_spec kn kn') as [E|E]; [now intros|].
  intros H. constructor; [cbn; intros ?; apply E; congruence | now apply IH].
Qed.

Lemma lookup_fresh_global kn Σ : fresh_global kn Σ -> lookup_env Σ kn = None.
Proof.
  induction 1 as [|[kn' d] Σ H1 _ IH]; [reflexivity|].
  cbn [lookup_env fst snd]. destruct (eqb_spec kn kn') as [E|E]; [cbn in H1; congruence | auto].
Qed.

Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l l' n x :
  Forall2 R l l' -> nth_error l n = Some x -> exists y, nth_error l' n = Some y /\ R x y.
Proof.
  induction 1 in n |- *; destruct n; cbn; try discriminate.
  - intros [= ->]. eauto.
  - auto.
Qed.

Lemma Forall2_rev' {A B} (R : A -> B -> Prop) l l' :
  Forall2 R l l' -> Forall2 R (rev l) (rev l').
Proof.
  induction 1; [constructor|].
  rewrite !rev_cons. apply Forall2_app; auto.
Qed.

Lemma All_Forall2_map {A} (P : A -> Type) (R : A -> A -> Prop) (f : A -> A) l :
  All P l -> (forall x, P x -> R x (f x)) -> Forall2 R l (map f l).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma All_Forall2_map2 {A} (P : A -> Type) (R S : A -> A -> Prop) (f g : A -> A) l l' :
  All P l -> Forall2 R l l' -> (forall x y, P x -> R x y -> S (f x) (g y)) ->
  Forall2 S (map f l) (map g l').
Proof.
  intros X; induction X in l' |- *; intros H; inversion H; subst; cbn; constructor; auto.
Qed.

Lemma All_Forall2_refl {A} (P : A -> Type) (R : A -> A -> Prop) l :
  All P l -> (forall x, P x -> R x x) -> Forall2 R l l.
Proof. induction 1; constructor; auto. Qed.

Lemma All_Forall2_impl {A} (P : A -> Type) (R S : A -> A -> Prop) l l' :
  All P l -> Forall2 R l l' -> (forall x y, P x -> R x y -> S x y) -> Forall2 S l l'.
Proof.
  intros X; induction X in l' |- *; intros H; inversion H; subst; constructor; auto.
Qed.

Lemma All_In_inv {A} (P : A -> Type) l x : All P l -> In x l -> ∥ P x ∥.
Proof. intros. now eapply All_In. Qed.

(** Unfolding equations. *)

Lemma collect_values_unfold t :
  collect_values t =
  if liftable t then [t] else
  match t with
  | tEvar _ ts => flat_map collect_values ts
  | tLambda _ b => collect_values b
  | tLetIn _ v b => collect_values v ++ collect_values b
  | tApp f a => collect_values f ++ collect_values a
  | tCase _ d brs => collect_values d ++ flat_map (fun br => collect_values (snd br)) brs
  | tProj _ u => collect_values u
  | tFix mf _ => flat_map (fun d => collect_values (dbody d)) mf
  | tCoFix mf _ => flat_map (fun d => collect_values (dbody d)) mf
  | tConstruct _ _ args => flat_map collect_values args
  | tLazy u => collect_values u
  | tForce u => collect_values u
  | _ => []
  end.
Proof. destruct t; reflexivity. Qed.

Lemma replace_unfold tbl t :
  replace tbl t =
  if liftable t then
    match lookup_table tbl t with
    | Some kn => tConst kn
    | None => t
    end
  else
  match t with
  | tPrim _ => t
  | _ => EBeta.map_subterms (replace tbl) t
  end.
Proof. destruct t; reflexivity. Qed.

(** Closed constructor values, as booleans. *)

Lemma is_cvalue_sizes l : isSome (cvalue_sizes l) = forallb is_cvalue l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  rewrite cvalue_sizes_cons. cbn. unfold is_cvalue.
  destruct (cvalue_size a), (cvalue_sizes l); cbn in *; auto; try now rewrite andb_false_r.
Qed.

Lemma is_cvalue_construct ind c args :
  is_cvalue (tConstruct ind c args) = forallb is_cvalue args.
Proof.
  unfold is_cvalue at 1. rewrite cvalue_size_construct -is_cvalue_sizes.
  now destruct (cvalue_sizes args).
Qed.

Lemma liftable_is_cvalue t : liftable t -> is_cvalue t.
Proof. unfold liftable, is_cvalue. now destruct (cvalue_size t). Qed.

Lemma is_cvalue_size t : is_cvalue t -> exists n, cvalue_size t = Some n.
Proof. unfold is_cvalue. destruct (cvalue_size t); [eauto|discriminate]. Qed.

Lemma liftable_construct_nil ind c : liftable (tConstruct ind c []) = false.
Proof. reflexivity. Qed.

Lemma liftable_box : liftable tBox = false.
Proof. reflexivity. Qed.

Lemma liftable_construct_inv t : liftable t -> exists ind c args, t = tConstruct ind c args.
Proof. destruct t; cbn; try discriminate; eauto. Qed.

(** Soundness of the table lookup. *)

Lemma cvalue_eqb_sound t u : cvalue_eqb t u -> t = u.
Proof.
  induction t using term_forall_list_ind in u |- *; destruct u; cbn; try discriminate; auto.
  move/andP => [/andP [Hi Hn] Hl].
  apply eqb_eq in Hi. apply Nat.eqb_eq in Hn. subst.
  f_equal. match goal with |- _ = ?l => revert l Hl end.
  induction X; intros l0 Hl; destruct l0; cbn in *; try discriminate; auto.
  move/andP: Hl => [Ha Hl]. f_equal; auto.
Qed.

Lemma lookup_table_sound tbl t kn : lookup_table tbl t = Some kn -> In (t, kn) tbl.
Proof.
  unfold lookup_table. destruct find as [[v kn']|] eqn:E; [|discriminate].
  intros [= <-]. apply find_some in E as [Hin Heq]. cbn in Heq.
  apply cvalue_eqb_sound in Heq. now subst.
Qed.

(** ** (4) The simulation relation

    [lift_rel Σ' t t'] holds when [t'] is [t] in which some liftable closed
    constructor values have been replaced by references to constants of [Σ']
    whose bodies are those values. *)

Inductive lift_rel (Σ' : global_declarations) : term -> term -> Prop :=
| lift_rel_lifted t kn :
    liftable t ->
    lookup_env Σ' kn = Some (ConstantDecl {| cst_body := Some t |}) ->
    lift_rel Σ' t (tConst kn)
| lift_rel_box : lift_rel Σ' tBox tBox
| lift_rel_rel n : lift_rel Σ' (tRel n) (tRel n)
| lift_rel_var na : lift_rel Σ' (tVar na) (tVar na)
| lift_rel_const kn : lift_rel Σ' (tConst kn) (tConst kn)
| lift_rel_evar n ts ts' : Forall2 (lift_rel Σ') ts ts' -> lift_rel Σ' (tEvar n ts) (tEvar n ts')
| lift_rel_lambda na b b' : lift_rel Σ' b b' -> lift_rel Σ' (tLambda na b) (tLambda na b')
| lift_rel_letin na v v' b b' :
    lift_rel Σ' v v' -> lift_rel Σ' b b' -> lift_rel Σ' (tLetIn na v b) (tLetIn na v' b')
| lift_rel_app f f' a a' :
    lift_rel Σ' f f' -> lift_rel Σ' a a' -> lift_rel Σ' (tApp f a) (tApp f' a')
| lift_rel_case ci d d' brs brs' :
    lift_rel Σ' d d' ->
    Forall2 (fun br br' => br.1 = br'.1 /\ lift_rel Σ' br.2 br'.2) brs brs' ->
    lift_rel Σ' (tCase ci d brs) (tCase ci d' brs')
| lift_rel_proj p u u' : lift_rel Σ' u u' -> lift_rel Σ' (tProj p u) (tProj p u')
| lift_rel_fix mf mf' idx :
    Forall2 (fun d d' => dname d = dname d' /\ rarg d = rarg d' /\ lift_rel Σ' (dbody d) (dbody d')) mf mf' ->
    lift_rel Σ' (tFix mf idx) (tFix mf' idx)
| lift_rel_cofix mf mf' idx :
    Forall2 (fun d d' => dname d = dname d' /\ rarg d = rarg d' /\ lift_rel Σ' (dbody d) (dbody d')) mf mf' ->
    lift_rel Σ' (tCoFix mf idx) (tCoFix mf' idx)
| lift_rel_construct ind c args args' :
    Forall2 (lift_rel Σ') args args' -> lift_rel Σ' (tConstruct ind c args) (tConstruct ind c args')
| lift_rel_prim_int i : lift_rel Σ' (tPrim (prim_int i)) (tPrim (prim_int i))
| lift_rel_prim_float f : lift_rel Σ' (tPrim (prim_float f)) (tPrim (prim_float f))
| lift_rel_prim_string s : lift_rel Σ' (tPrim (prim_string s)) (tPrim (prim_string s))
| lift_rel_prim_array d d' v v' :
    lift_rel Σ' d d' -> Forall2 (lift_rel Σ') v v' ->
    lift_rel Σ' (tPrim (prim_array {| array_default := d; array_value := v |}))
      (tPrim (prim_array {| array_default := d'; array_value := v' |}))
| lift_rel_lazy u u' : lift_rel Σ' u u' -> lift_rel Σ' (tLazy u) (tLazy u')
| lift_rel_force u u' : lift_rel Σ' u u' -> lift_rel Σ' (tForce u) (tForce u').

Ltac not_lifted :=
  match goal with
  | H : context [liftable _] |- _ => cbn in H; discriminate
  end.

Section LiftRel.
  Variable Σ' : global_declarations.
  Notation R := (lift_rel Σ').

  Lemma lift_rel_refl t : R t t.
  Proof.
    induction t using term_forall_list_ind; try now constructor.
    all: try (constructor; eauto; eapply All_Forall2_refl; tea; cbn; intuition eauto; fail).
    destruct p as [? []]; try constructor. depelim X. destruct p as [Hd Hv].
    destruct a; cbn in *. constructor; auto.
    eapply All_Forall2_refl; tea. auto.
  Qed.

  Lemma Forall2_lift_rel_refl l : Forall2 R l l.
  Proof. induction l; constructor; auto using lift_rel_refl. Qed.

  Lemma lift_rel_mkApps f f' args args' :
    R f f' -> Forall2 R args args' -> R (mkApps f args) (mkApps f' args').
  Proof.
    intros Hf H. induction H in f, f', Hf |- *; cbn; auto.
    apply IHForall2. now constructor.
  Qed.

  Lemma lift_rel_mkApps_inv f args t' :
    R (mkApps f args) t' ->
    exists f' args', t' = mkApps f' args' /\ R f f' /\ Forall2 R args args'.
  Proof.
    revert t'; induction args as [|a args IH] using rev_ind; intros t'.
    - intros H. exists t', []. cbn. auto.
    - rewrite mkApps_app. cbn. intros H. inversion H; subst; try not_lifted.
      destruct (IH _ H2) as (f'' & args'' & -> & Hf & Hargs).
      exists f'', (args'' ++ [a']). rewrite mkApps_app. repeat split; auto.
      apply Forall2_app; auto.
  Qed.

  Ltac lifted_closed :=
    match goal with Hl : context [liftable _] |- _ =>
      let Hm := fresh "Hm" in
      destruct (is_cvalue_size _ (liftable_is_cvalue _ Hl)) as [? Hm];
      rewrite (cvalue_csubst _ _ _ _ Hm); cbn; now constructor
    end.

  Lemma lift_rel_csubst a a' k t t' :
    R a a' -> R t t' -> R (csubst a k t) (csubst a' k t').
  Proof.
    intros Ha. induction t using term_forall_list_ind in k, t' |- *; intros H;
      inversion H; subst; try not_lifted; try lifted_closed.
    all: cbn; try (constructor; eauto; fail).
    all: try (destruct (Nat.compare k n); auto; constructor; fail).
    all: try (constructor; eapply All_Forall2_map2; eauto; fail).
    all: try (constructor; auto; eapply All_Forall2_map2; eauto; cbn;
              intros x y Hx [Hxy Hr]; split; auto; rewrite Hxy; now apply Hx).
    all: try (constructor; match goal with H : Forall2 _ ?l ?l' |- _ => rewrite -(Forall2_length H) end;
              eapply All_Forall2_map2; eauto; cbn; intros x y Hx (? & ? & ?); auto; fail).
    all: depelim X; match goal with p : _ × _ |- _ => destruct p as [Hd Hv] end;
      unfold map_array_model; cbn; constructor; [now apply Hd | eapply All_Forall2_map2; eauto].
  Qed.

  Lemma lift_rel_substl s s' t t' :
    Forall2 R s s' -> R t t' -> R (substl s t) (substl s' t').
  Proof.
    unfold substl. intros H. induction H in t, t' |- *; cbn; auto.
    intros Ht. apply IHForall2. now apply lift_rel_csubst.
  Qed.

  Definition fix_rel (mf mf' : mfixpoint term) :=
    Forall2 (fun d d' => dname d = dname d' /\ rarg d = rarg d' /\ R (dbody d) (dbody d')) mf mf'.

  Lemma lift_rel_fix_subst mf mf' : fix_rel mf mf' -> Forall2 R (fix_subst mf) (fix_subst mf').
  Proof.
    intros H. unfold fix_subst. rewrite (Forall2_length H).
    induction #|mf'|; constructor; auto. now constructor.
  Qed.

  Lemma lift_rel_cofix_subst mf mf' : fix_rel mf mf' -> Forall2 R (cofix_subst mf) (cofix_subst mf').
  Proof.
    intros H. unfold cofix_subst. rewrite (Forall2_length H).
    induction #|mf'|; constructor; auto. now constructor.
  Qed.

  Lemma lift_rel_cunfold_fix mf mf' idx narg fn :
    fix_rel mf mf' -> cunfold_fix mf idx = Some (narg, fn) ->
    exists fn', cunfold_fix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H. unfold cunfold_fix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-]. destruct (Forall2_nth_error_l _ _ _ _ _ H E) as (d' & -> & ? & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply lift_rel_substl; auto.
    now apply lift_rel_fix_subst.
  Qed.

  Lemma lift_rel_cunfold_cofix mf mf' idx narg fn :
    fix_rel mf mf' -> cunfold_cofix mf idx = Some (narg, fn) ->
    exists fn', cunfold_cofix mf' idx = Some (narg, fn') /\ R fn fn'.
  Proof.
    intros H. unfold cunfold_cofix. destruct nth_error eqn:E; [|discriminate].
    intros [= <- <-]. destruct (Forall2_nth_error_l _ _ _ _ _ H E) as (d' & -> & ? & Hr & Hb).
    eexists; split; [now rewrite Hr|]. apply lift_rel_substl; auto.
    now apply lift_rel_cofix_subst.
  Qed.

  (** Inversions. *)

  Lemma lift_rel_box_inv t' : R tBox t' -> t' = tBox.
  Proof. intros H; inversion H; subst; auto; not_lifted. Qed.

  Lemma lift_rel_lambda_inv na b t' : R (tLambda na b) t' -> exists b', t' = tLambda na b' /\ R b b'.
  Proof. intros H; inversion H; subst; try not_lifted; eauto. Qed.

  Lemma lift_rel_lazy_inv b t' : R (tLazy b) t' -> exists b', t' = tLazy b' /\ R b b'.
  Proof. intros H; inversion H; subst; try not_lifted; eauto. Qed.

  Lemma lift_rel_fix_inv mf idx t' : R (tFix mf idx) t' -> exists mf', t' = tFix mf' idx /\ fix_rel mf mf'.
  Proof. intros H; inversion H; subst; try not_lifted; eauto. Qed.

  Lemma lift_rel_cofix_inv mf idx t' : R (tCoFix mf idx) t' -> exists mf', t' = tCoFix mf' idx /\ fix_rel mf mf'.
  Proof. intros H; inversion H; subst; try not_lifted; eauto. Qed.

  Lemma lift_rel_construct_nil_inv ind c t' : R (tConstruct ind c []) t' -> t' = tConstruct ind c [].
  Proof.
    intros H; inversion H; subst; try not_lifted.
    match goal with H : Forall2 _ [] _ |- _ => now inversion H end.
  Qed.

  Lemma lift_rel_construct_inv ind c args t' :
    R (tConstruct ind c args) t' -> (forall kn, t' <> tConst kn) ->
    exists args', t' = tConstruct ind c args' /\ Forall2 R args args'.
  Proof. intros H Hn; inversion H; subst; eauto. now elim (Hn kn). Qed.

  Lemma lift_rel_isLambda b b' : R b b' -> isLambda b = isLambda b'.
  Proof.
    intros H; inversion H; subst; auto.
    apply liftable_construct_inv in H0 as (? & ? & ? & ->). reflexivity.
  Qed.

  Lemma lift_rel_head f f' :
    R f f' -> (forall kn, head f' <> tConst kn) -> R (head f) (head f').
  Proof.
    induction f using term_forall_list_ind in f' |- *; intros H Hn;
      inversion H; subst; cbn in Hn |- *;
      try solve [now elim (Hn kn) | exact H].
    rewrite !head_tApp in Hn |- *. auto.
  Qed.

  Lemma lift_rel_shape t t' :
    R t t' -> (forall kn, t' <> tConst kn) ->
    [/\ isLambda t = isLambda t', isFix t = isFix t', isBox t = isBox t',
        isConstruct t = isConstruct t', isPrim t = isPrim t' & isLazy t = isLazy t'].
  Proof.
    intros H Hn; inversion H; subst; try (now elim (Hn kn)); split; reflexivity.
  Qed.

End LiftRel.

(** ** (5) Evaluation under environments with the same inductives *)

Section SameInductives.
  Variables Σ Σ' : global_declarations.
  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.

  Lemma same_lookup_inductive ind : lookup_inductive Σ ind = lookup_inductive Σ' ind.
  Proof. unfold lookup_inductive. now rewrite Hind. Qed.

  Lemma same_lookup_constructor ind c : lookup_constructor Σ ind c = lookup_constructor Σ' ind c.
  Proof. unfold lookup_constructor. now rewrite same_lookup_inductive. Qed.

  Lemma same_lookup_constructor_pars_args ind c :
    lookup_constructor_pars_args Σ ind c = lookup_constructor_pars_args Σ' ind c.
  Proof. unfold lookup_constructor_pars_args. now rewrite same_lookup_constructor. Qed.

  Lemma same_lookup_projection p : lookup_projection Σ p = lookup_projection Σ' p.
  Proof. unfold lookup_projection. now rewrite same_lookup_constructor. Qed.

  Lemma same_constructor_isprop_pars_decl ind c :
    constructor_isprop_pars_decl Σ ind c = constructor_isprop_pars_decl Σ' ind c.
  Proof. unfold constructor_isprop_pars_decl. now rewrite same_lookup_constructor. Qed.

  Lemma same_inductive_isprop_and_pars ind :
    inductive_isprop_and_pars Σ ind = inductive_isprop_and_pars Σ' ind.
  Proof. unfold inductive_isprop_and_pars. now rewrite same_lookup_inductive. Qed.

  Lemma same_atom {wfl : WcbvFlags} t : atom Σ t = atom Σ' t.
  Proof. unfold atom. destruct t; try reflexivity. now rewrite same_lookup_constructor. Qed.

  (** A closed constructor value evaluates in the same way in both
      environments. *)
  Lemma cvalue_eval_transfer {wfl : WcbvFlags} t v :
    eval Σ t v -> is_cvalue t -> eval Σ' t v.
  Proof.
    intros ev. induction ev; intros Hc; try (cbn in Hc; discriminate).
    - rewrite is_cvalue_construct in Hc.
      eapply eval_construct_block; tea. now rewrite -same_lookup_constructor.
      clear -iha Hc. induction a; constructor; cbn in iha, Hc; move/andP: Hc => [Hx Hl];
        destruct iha; auto.
    - apply eval_atom. now rewrite -same_atom.
  Qed.

End SameInductives.


(** ** (6) Simulation *)

Lemma value_head_not_const {wfl : WcbvFlags} Σ v : value Σ v -> forall kn, head v <> tConst kn.
Proof.
  intros H. revert v H.
  apply (value_values_ind (fun v => forall kn, head v <> tConst kn)).
  - intros t H kn. destruct t; cbn in H; try discriminate; rewrite head_nApp_eq //.
  - intros p _ _ kn. rewrite head_nApp_eq //.
  - intros. rewrite head_nApp_eq //.
  - intros f args vh _ _ _ kn. rewrite head_mkApps. rewrite head_nApp_eq; [eapply value_head_nApp; tea|].
    destruct vh; discriminate.
Qed.

Lemma eval_not_const {wfl : WcbvFlags} Σ t v : eval Σ t v -> forall kn, head v <> tConst kn.
Proof. intros ev. now eapply value_head_not_const, eval_to_value. Qed.

Lemma head_const_not_const t : (forall kn, head t <> tConst kn) -> forall kn, t <> tConst kn.
Proof. intros H kn ->. now apply (H kn). Qed.

Lemma isFixApp_isFix t : isFixApp t = isFix (head t).
Proof. reflexivity. Qed.

Lemma Forall2_List_rev {A B} (P : A -> B -> Prop) l l' :
  Forall2 P l l' -> Forall2 P (List.rev l) (List.rev l').
Proof. induction 1; cbn; [constructor|]. apply Forall2_app; auto. Qed.

Section Simulation.
  Context {wfl : WcbvFlags}.
  Variables Σ Σ' : global_declarations.
  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall kn b,
    declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σ' kn {| cst_body := Some b' |} /\ lift_rel Σ' b b'.

  Notation R := (lift_rel Σ').

  Lemma app_cong_shape f f' :
    R f f' -> (forall kn, head f' <> tConst kn) ->
    [/\ isLambda f = isLambda f', isFixApp f = isFixApp f', isFix f = isFix f', isBox f = isBox f',
      isConstructApp f = isConstructApp f', isPrimApp f = isPrimApp f' & isLazyApp f = isLazyApp f'].
  Proof.
    intros H Hn.
    have Hh := lift_rel_head _ _ _ H Hn.
    have [? ? ? ? ? ?] := lift_rel_shape _ _ _ Hh Hn.
    have [? ? ? ? ? ?] := lift_rel_shape _ _ _ H (head_const_not_const _ Hn).
    unfold isFixApp, isConstructApp, isPrimApp, isLazyApp. split; auto.
  Qed.

  Definition sim_goal t v :=
    forall t', R t t' -> exists v', ∥ eval Σ' t' v' ∥ /\ R v v'.

  Lemma sim_args args args' :
    forall (a : All2_Set (eval Σ) args args'),
    All2_over a (fun x y _ => sim_goal x y) ->
    forall args0, Forall2 R args args0 ->
    exists args1, ∥ All2_Set (eval Σ') args0 args1 ∥ /\ Forall2 R args' args1.
  Proof.
    induction a; cbn; intros iha args0 H.
    - inversion H; subst. exists []. split; [sq; constructor | constructor].
    - destruct iha as [hx hl]. inversion H; subst.
      destruct (hx _ H2) as (y' & [evy] & Hy).
      destruct (IHa hl _ H4) as (lr & [evl] & Hl).
      exists (y' :: lr). split; [sq; now constructor | now constructor].
  Qed.

  Ltac sim_ih IH H :=
    let v := fresh "v" in let ev := fresh "ev" in let Hv := fresh "Hv" in
    destruct (IH _ H) as (v & [ev] & Hv).

  Lemma lift_rel_construct_value ind c args v :
    R (tConstruct ind c args) v -> (forall kn, head v <> tConst kn) ->
    exists args', v = tConstruct ind c args' /\ Forall2 R args args'.
  Proof.
    intros H Hn. eapply lift_rel_construct_inv; tea. now apply head_const_not_const.
  Qed.

  Lemma lift_rel_mkApps_construct_nil ind c args v :
    R (mkApps (tConstruct ind c []) args) v ->
    exists args', v = mkApps (tConstruct ind c []) args' /\ Forall2 R args args'.
  Proof.
    intros H. destruct (lift_rel_mkApps_inv _ _ _ _ H) as (f' & args' & -> & Hf & Ha).
    apply lift_rel_construct_nil_inv in Hf as ->. eauto.
  Qed.

  Lemma lift_rel_mkApps_fix mfix idx args v :
    R (mkApps (tFix mfix idx) args) v ->
    exists mfix' args', v = mkApps (tFix mfix' idx) args' /\ fix_rel Σ' mfix mfix' /\ Forall2 R args args'.
  Proof.
    intros H. destruct (lift_rel_mkApps_inv _ _ _ _ H) as (f' & args' & -> & Hf & Ha).
    apply lift_rel_fix_inv in Hf as (mf' & -> & Hmf). eauto 6.
  Qed.

  Lemma lift_rel_mkApps_cofix mfix idx args v :
    R (mkApps (tCoFix mfix idx) args) v ->
    exists mfix' args', v = mkApps (tCoFix mfix' idx) args' /\ fix_rel Σ' mfix mfix' /\ Forall2 R args args'.
  Proof.
    intros H. destruct (lift_rel_mkApps_inv _ _ _ _ H) as (f' & args' & -> & Hf & Ha).
    apply lift_rel_cofix_inv in Hf as (mf' & -> & Hmf). eauto 6.
  Qed.

  Lemma lift_rel_iota_red pars args args' br br' :
    Forall2 R args args' -> br.1 = br'.1 -> R br.2 br'.2 ->
    R (iota_red pars args br) (iota_red pars args' br').
  Proof.
    intros Ha _ Hb. unfold iota_red. apply lift_rel_substl; auto.
    apply Forall2_List_rev, Forall2_skipn, Ha.
  Qed.

  Ltac sims := repeat match goal with
    | IH : forall t', lift_rel _ ?x t' -> exists _, _ , H : lift_rel _ ?x ?y |- _ =>
      let w := fresh "w" in let ew := fresh "ew" in let Hw := fresh "Hw" in
      destruct (IH _ H) as (w & [ew] & Hw); clear IH
    end.

  Ltac len_tac := match goal with
    | H : Forall2 _ ?l ?l' |- context [#|?l'|] => rewrite -(Forall2_length H)
    end.

  Ltac branch_tac :=
    match goal with
    | e : nth_error ?l ?c = Some ?br, H : Forall2 _ ?l ?l' |- _ =>
      destruct (Forall2_nth_error_l _ _ _ _ _ H e) as (brL & HbrL & HbrL1 & HbrL2)
    end.

  Ltac ind_tac := first [ now rewrite -(same_constructor_isprop_pars_decl _ _ Hind)
                        | now rewrite -(same_inductive_isprop_and_pars _ _ Hind)
                        | now rewrite -(same_lookup_constructor _ _ Hind) ].

  Lemma lift_rel_simulation t v :
    eval Σ t v -> sim_goal t v.
  Proof.
    intros ev. unfold sim_goal.
    induction ev using eval_rect; intros t0 Ht.
    all: try (inversion Ht; subst; try not_lifted).
    all: sims.
    (* atom cases (the inversion above split them per constructor) *)
    all: try solve [
      match goal with H : context [liftable _], i : context [atom _ _] |- _ =>
        pose proof H as Hl; apply liftable_construct_inv in H as (? & ? & argsL & ->);
        destruct argsL; [rewrite liftable_construct_nil in Hl; discriminate | unfold atom in i; discriminate] end
    | match goal with i : context [atom _ _] |- _ => unfold atom in i; discriminate end
    | match goal with i : context [atom _ _] |- _ =>
        eexists; split; [sq; apply eval_atom; reflexivity|exact Ht] end
    | match goal with i : context [atom _ (tConstruct _ _ ?args)] |- _ =>
        destruct args; [| unfold atom in i; discriminate];
        match goal with H : Forall2 _ [] _ |- _ => inversion H; subst end;
        eexists; split; [sq; apply eval_atom; rewrite -(same_atom _ _ Hind); exact i | exact Ht] end ].
    - (* box *)
      match goal with H : R tBox _ |- _ => apply lift_rel_box_inv in H; subst end.
      exists tBox. split; [sq; econstructor; tea | constructor].
    - (* beta *)
      match goal with H : R (tLambda _ _) _ |- _ => apply lift_rel_lambda_inv in H as (bL & -> & HbL) end.
      match goal with H : R ?a ?a', IH : forall t', R (csubst ?a 0 ?b) t' -> _ |- _ =>
        destruct (IH (csubst a' 0 bL)) as (r & [evr] & Hr); [now apply lift_rel_csubst|] end.
      exists r. split; [sq; econstructor; tea | auto].
    - (* zeta *)
      match goal with H : R ?a ?a', H' : R ?b ?bL, IH : forall t', R (csubst ?a 0 ?b) t' -> _ |- _ =>
        destruct (IH (csubst a' 0 bL)) as (r & [evr] & Hr); [now apply lift_rel_csubst|] end.
      exists r. split; [sq; econstructor; tea | auto].
    - (* iota *)
      match goal with H : R (mkApps (tConstruct _ _ []) _) _ |- _ =>
        destruct (lift_rel_mkApps_construct_nil _ _ _ _ H) as (argsL & -> & HargsL) end.
      branch_tac.
      match goal with IH : forall t', R (iota_red ?pars _ _) t' -> _ |- _ =>
        destruct (IH (iota_red pars argsL brL)) as (r & [evr] & Hr); [now apply lift_rel_iota_red|] end.
      exists r. split; [|auto]. sq. eapply eval_iota; tea.
      + ind_tac.
      + now len_tac.
      + rewrite -HbrL1. rewrite -(Forall2_length (Forall2_skipn _ _ _ _ _ pars HargsL)). auto.
    - (* iota block *)
      match goal with H : R (tConstruct _ _ _) ?w, ew : eval Σ' _ ?w |- _ =>
        destruct (lift_rel_construct_value _ _ _ _ H (eval_not_const _ _ _ ew)) as (argsL & -> & HargsL) end.
      branch_tac.
      match goal with IH : forall t', R (iota_red ?pars _ _) t' -> _ |- _ =>
        destruct (IH (iota_red pars argsL brL)) as (r & [evr] & Hr); [now apply lift_rel_iota_red|] end.
      exists r. split; [|auto]. sq. eapply eval_iota_block; tea.
      + ind_tac.
      + now len_tac.
      + rewrite -HbrL1. rewrite -(Forall2_length (Forall2_skipn _ _ _ _ _ pars HargsL)). auto.
    - (* iota sing *)
      match goal with H : R tBox _ |- _ => apply lift_rel_box_inv in H; subst end.
      match goal with H : Forall2 _ [_] _ |- _ =>
        inversion H as [|? brL ? brsL HbrL Hnil]; subst; inversion Hnil; subst end.
      destruct brL as [nL fL]. destruct HbrL as [HnL HfL]. cbn in HnL, HfL. subst nL.
      match goal with IH : forall t', R (substl (repeat tBox #|?n|) ?f) t' -> _ |- _ =>
        destruct (IH (substl (repeat tBox #|n|) fL)) as (r & [evr] & Hr);
        [apply lift_rel_substl; auto; apply Forall2_lift_rel_refl|] end.
      exists r. split; [|auto]. sq. eapply eval_iota_sing; tea; [ind_tac|reflexivity].
    - (* fix *)
      match goal with H : R (mkApps (tFix _ _) _) _ |- _ =>
        destruct (lift_rel_mkApps_fix _ _ _ _ H) as (mfL & argsL & -> & HmfL & HargsL) end.
      match goal with e : cunfold_fix _ _ = Some _ |- _ =>
        destruct (lift_rel_cunfold_fix _ _ _ _ _ _ HmfL e) as (fnL & HfnL & HfnL') end.
      match goal with H : R ?a ?a', IH : forall t', R (tApp (mkApps ?fn ?args) ?a) t' -> _ |- _ =>
        destruct (IH (tApp (mkApps fnL argsL) a')) as (r & [evr] & Hr);
        [constructor; auto; now apply lift_rel_mkApps|] end.
      exists r. split; [|auto]. sq. eapply eval_fix; tea. now len_tac.
    - (* fix value *)
      match goal with H : R (mkApps (tFix _ _) _) _ |- _ =>
        destruct (lift_rel_mkApps_fix _ _ _ _ H) as (mfL & argsL & -> & HmfL & HargsL) end.
      match goal with e : cunfold_fix _ _ = Some _ |- _ =>
        destruct (lift_rel_cunfold_fix _ _ _ _ _ _ HmfL e) as (fnL & HfnL & HfnL') end.
      eexists. split.
      + sq. eapply eval_fix_value; tea. now len_tac.
      + now constructor.
    - (* fix' *)
      match goal with H : R (tFix _ _) _ |- _ =>
        apply lift_rel_fix_inv in H as (mfL & -> & HmfL) end.
      match goal with e : cunfold_fix _ _ = Some _ |- _ =>
        destruct (lift_rel_cunfold_fix _ _ _ _ _ _ HmfL e) as (fnL & HfnL & HfnL') end.
      match goal with H : R ?a ?a', IH : forall t', R (tApp ?fn ?a) t' -> _ |- _ =>
        destruct (IH (tApp fnL a')) as (r & [evr] & Hr); [now constructor|] end.
      exists r. split; [|auto]. sq. eapply eval_fix'; tea.
    - (* cofix case *)
      match goal with H : R (mkApps (tCoFix _ _) _) _ |- _ =>
        destruct (lift_rel_mkApps_cofix _ _ _ _ H) as (mfL & argsL & -> & HmfL & HargsL) end.
      match goal with e : cunfold_cofix _ _ = Some _ |- _ =>
        destruct (lift_rel_cunfold_cofix _ _ _ _ _ _ HmfL e) as (fnL & HfnL & HfnL') end.
      match goal with H : Forall2 _ ?brs ?brs', IH : forall t', R (tCase ?ip (mkApps ?fn ?args) ?brs) t' -> _ |- _ =>
        destruct (IH (tCase ip (mkApps fnL argsL) brs')) as (r & [evr] & Hr);
        [constructor; auto; now apply lift_rel_mkApps|] end.
      exists r. split; [|auto]. sq. eapply eval_cofix_case; tea.
    - (* cofix proj *)
      match goal with H : R (mkApps (tCoFix _ _) _) _ |- _ =>
        destruct (lift_rel_mkApps_cofix _ _ _ _ H) as (mfL & argsL & -> & HmfL & HargsL) end.
      match goal with e : cunfold_cofix _ _ = Some _ |- _ =>
        destruct (lift_rel_cunfold_cofix _ _ _ _ _ _ HmfL e) as (fnL & HfnL & HfnL') end.
      match goal with IH : forall t', R (tProj ?p (mkApps ?fn ?args)) t' -> _ |- _ =>
        destruct (IH (tProj p (mkApps fnL argsL))) as (r & [evr] & Hr);
        [constructor; auto; now apply lift_rel_mkApps|] end.
      exists r. split; [|auto]. sq. eapply eval_cofix_proj; tea.
    - (* delta *)
      match goal with d : constant_body |- _ => destruct d as [body0] end.
      cbn in *. subst.
      match goal with H : declared_constant Σ _ _ |- _ => destruct (Hcst _ _ H) as (bL & HdL & HbL) end.
      match goal with IH : forall t', R ?b t' -> _ |- _ =>
        destruct (IH _ HbL) as (r & [evr] & Hr) end.
      exists r. split; [|auto]. sq. eapply eval_delta; tea. reflexivity.
    - (* proj *)
      match goal with H : R (mkApps (tConstruct _ _ []) _) _ |- _ =>
        destruct (lift_rel_mkApps_construct_nil _ _ _ _ H) as (argsL & -> & HargsL) end.
      match goal with e : nth_error ?l _ = Some _ |- _ =>
        destruct (Forall2_nth_error_l _ _ _ _ _ HargsL e) as (aL & HaL & HaL') end.
      sims.
      eexists. split; [|eassumption]. sq. eapply eval_proj; tea.
      + ind_tac.
      + now len_tac.
    - (* proj block *)
      match goal with H : R (tConstruct _ _ _) ?w, ew : eval Σ' _ ?w |- _ =>
        destruct (lift_rel_construct_value _ _ _ _ H (eval_not_const _ _ _ ew)) as (argsL & -> & HargsL) end.
      match goal with e : nth_error ?l _ = Some _ |- _ =>
        destruct (Forall2_nth_error_l _ _ _ _ _ HargsL e) as (aL & HaL & HaL') end.
      sims.
      eexists. split; [|eassumption]. sq. eapply eval_proj_block; tea.
      + ind_tac.
      + now len_tac.
    - (* proj prop *)
      match goal with H : R tBox _ |- _ => apply lift_rel_box_inv in H; subst end.
      exists tBox. split; [|constructor]. sq. eapply eval_proj_prop; tea. ind_tac.
    - (* construct *)
      match goal with H : R (mkApps (tConstruct _ _ []) _) _ |- _ =>
        destruct (lift_rel_mkApps_construct_nil _ _ _ _ H) as (argsL & -> & HargsL) end.
      eexists. split.
      + sq. eapply eval_construct; tea.
        * ind_tac.
        * now len_tac.
      + now constructor.
    - (* construct block, lifted *)
      eexists. split; [|apply lift_rel_refl].
      sq. eapply eval_delta; [eassumption|reflexivity|].
      eapply cvalue_eval_transfer; [exact Hind| |now apply liftable_is_cvalue].
      eapply eval_construct_block; tea.
    - (* construct block, congruence *)
      match goal with H : Forall2 _ ?args _ |- _ =>
        destruct (sim_args _ _ a iha _ H) as (args1 & [evs] & Hargs1) end.
      eexists. split; [|now constructor].
      sq. eapply eval_construct_block; tea.
      + ind_tac.
      + now len_tac.
    - (* app cong *)
      match goal with H : R ?f ?w, ew : eval Σ' _ ?w |- context [tApp ?f _] =>
        have [E1 E2 E3 E4 E5 E6 E7] := app_cong_shape _ _ H (eval_not_const _ _ _ ew) end.
      eexists. split; [|now constructor].
      sq. eapply eval_app_cong; tea.
      rewrite -E1 -E2 -E3 -E4 -E5 -E6 -E7. assumption.
    - (* prim int *)
      depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - depelim X. eexists. split; [sq; eapply eval_prim; constructor|constructor].
    - (* prim array *)
      depelim X.
      match goal with ev : All2_Set _ ?v _, a : All2_over ?ev _, H : Forall2 _ ?v _ |- _ =>
        destruct (sim_args _ _ ev a _ H) as (v1 & [evs] & Hv1) end.
      match goal with IH : forall t', R ?d t' -> _, H : R ?d ?d' |- _ =>
        destruct (IH _ H) as (d1 & [evd] & Hd1) end.
      exists (tPrim (prim_array {| array_default := d1; array_value := v1 |})).
      split; [sq; eapply eval_prim; now constructor|now constructor].
    - (* force *)
      match goal with H : R (tLazy _) _ |- _ => apply lift_rel_lazy_inv in H as (bL & -> & HbL) end.
      sims.
      eexists. split; [|eassumption]. sq. eapply eval_force; tea.
  Qed.

End Simulation.


(** ** (7) Monotonicity and well-formedness of related terms *)

Definition env_ext (Σa Σb : global_declarations) :=
  forall kn d, lookup_env Σa kn = Some d -> lookup_env Σb kn = Some d.

Lemma env_ext_refl Σ : env_ext Σ Σ.
Proof. now intros ? ?. Qed.

Lemma env_ext_trans Σa Σb Σc : env_ext Σa Σb -> env_ext Σb Σc -> env_ext Σa Σc.
Proof. intros H1 H2 kn d H. now apply H2, H1. Qed.

Lemma env_ext_app_fresh Σ1 Σ2 :
  (forall kn, In kn (map fst Σ1) -> lookup_env Σ2 kn = None) -> env_ext Σ2 (Σ1 ++ Σ2).
Proof.
  intros Hf kn d H. rewrite lookup_env_app_fresh; auto.
  apply Forall_forall. intros [kn' d'] Hin E. cbn in E. subst kn'.
  rewrite Hf in H; [|discriminate].
  apply in_map_iff. now exists (kn, d').
Qed.

Lemma env_ext_cons_fresh kn d Σ : lookup_env Σ kn = None -> env_ext Σ ((kn, d) :: Σ).
Proof.
  intros Hf kn' d' H. cbn [lookup_env fst snd].
  destruct (eqb_spec kn' kn) as [->|E]; [congruence|auto].
Qed.

Lemma lift_rel_mono Σa Σb t t' : env_ext Σa Σb -> lift_rel Σa t t' -> lift_rel Σb t t'.
Proof.
  intros He. induction t using term_forall_list_ind in t' |- *; intros H;
    inversion H; subst; try (econstructor; [assumption | now apply He]).
  all: try (constructor; eauto; fail).
  all: try (constructor; eauto; eapply All_Forall2_impl; tea; cbn; intuition eauto; fail).
  all: depelim X; match goal with p : _ × _ |- _ => destruct p as [Hd Hv] end;
    constructor; [now apply Hd | eapply All_Forall2_impl; tea; cbn; eauto].
Qed.

Lemma Forall2_forallb {A} (P : A -> Type) (R : A -> A -> Prop) (f g : A -> bool) l l' :
  All P l -> Forall2 R l l' -> (forall x y, P x -> R x y -> f x -> g y) ->
  forallb f l -> forallb g l'.
Proof.
  intros X; induction X in l' |- *; intros H Hi; inversion H; subst; cbn; auto.
  move/andP => [Hx Hl]. apply/andP; split; eauto.
Qed.

Section WfRel.
  Context {efl : EEnvFlags}.
  Variables Σ Σ' : global_declarations.
  Hypothesis Hind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ' kn.
  Hypothesis Hcst : forall kn,
    match lookup_constant Σ kn with Some d => has_axioms || isSome d.(cst_body) | _ => false end ->
    match lookup_constant Σ' kn with Some d => has_axioms || isSome d.(cst_body) | _ => false end.
  Hypothesis HtConst : has_tConst.

  Ltac flen := match goal with H : Forall2 _ ?l ?l' |- context [#|?l'|] => rewrite -(Forall2_length H) end.

  Lemma wellformed_lift_rel t t' k :
    lift_rel Σ' t t' -> wellformed Σ k t -> wellformed Σ' k t'.
  Proof.
    induction t using term_forall_list_ind in k, t' |- *; intros H;
      inversion H; subst.
    all: try (cbn; unfold lookup_constant;
              match goal with H : lookup_env Σ' _ = Some _ |- _ => rewrite H end;
              cbn; rewrite HtConst; now rewrite orb_true_r).
    all: cbn -[lookup_constructor lookup_constructor_pars_args lookup_projection lookup_inductive lookup_constant]; auto.
    - move/andP => [-> Hl]. cbn. eapply Forall2_forallb; tea. cbn; eauto.
    - move/andP => [-> Hb]. cbn. eauto.
    - move/andP => [/andP [-> Hv] Hb]. cbn. apply/andP; split; eauto.
    - move/andP => [/andP [-> Hv] Hb]. cbn. apply/andP; split; eauto.
    - move/andP => [-> Hc]. now apply Hcst.
    - rewrite -(same_lookup_constructor _ _ Hind) -(same_lookup_constructor_pars_args _ _ Hind).
      move/andP => [/andP [-> ->] Ha]. cbn -[lookup_constructor_pars_args].
      destruct cstr_as_blocks; [|match goal with H : Forall2 _ _ _ |- _ => now destruct H; cbn in * end].
      move/andP: Ha => [Hpa Ha]. apply/andP; split.
      + destruct lookup_constructor_pars_args as [[]|]; auto. now flen.
      + eapply Forall2_forallb; tea. cbn; eauto.
    - move/and3P => [-> /andP [Hb Hw] Hf]. cbn.
      unfold wf_brs in *. rewrite -(same_lookup_inductive _ _ Hind). flen.
      rewrite Hb. cbn. apply/andP; split; eauto.
      eapply Forall2_forallb; tea. cbn. intros x y Hx [Hxy Hr]. rewrite -Hxy. eauto.
    - rewrite -(same_lookup_projection _ _ Hind).
      move/andP => [/andP [-> Hp] Hu]. cbn. rewrite Hp. cbn. eauto.
    - unfold wf_fix_gen. move/and3P => [/andP [Hh Hl] Hi Hf]. rewrite Hh /=. apply/and3P; split.
      + eapply Forall2_forallb; [tea|tea| |exact Hl]. cbn. intros x y _ (_ & _ & Hr).
        now rewrite (lift_rel_isLambda _ _ _ Hr).
      + now flen.
      + flen. eapply Forall2_forallb; tea. cbn.
        intros x y Hx (_ & _ & Hr). unfold test_def. eauto.
    - unfold wf_fix_gen. intros Hc; rtoProp. rewrite H0 /=. split; [done|split].
      + now flen.
      + flen. eapply Forall2_forallb; tea. cbn.
        intros x y Hx (_ & _ & Hr). unfold test_def. eauto.
    - depelim X. move/andP => [-> /andP [Hd Hv]]. cbn. destruct p as [Hd' Hv'].
      apply/andP; split; eauto. eapply Forall2_forallb; tea. cbn; eauto.
    - move/andP => [-> Hu]. cbn. eauto.
    - move/andP => [-> Hu]. cbn. eauto.
  Qed.
End WfRel.

Lemma cvalue_wellformed_transfer {efl : EEnvFlags} Σa Σb v k k' :
  (forall kn, lookup_minductive Σa kn = lookup_minductive Σb kn) ->
  is_cvalue v -> wellformed Σa k v -> wellformed Σb k' v.
Proof.
  intros Hind. induction v using term_forall_list_ind; cbn -[lookup_constructor lookup_constructor_pars_args is_cvalue]; try discriminate; auto.
  rewrite is_cvalue_construct.
  rewrite (same_lookup_constructor _ _ Hind) (same_lookup_constructor_pars_args _ _ Hind).
  intros Hc. move/andP => [-> Ha]. destruct cstr_as_blocks; auto.
  move/andP: Ha => [-> Ha]. cbn. clear -X Hc Ha.
  induction X; cbn in *; auto. move/andP: Hc => [Hx Hc]. move/andP: Ha => [Hx' Ha].
  apply/andP; split; auto.
Qed.


(** ** (8) The table, [replace], and the lifted declarations *)

Definition tbl_ok Σ' (tbl : table) :=
  forall v kn, In (v, kn) tbl ->
    liftable v /\ lookup_env Σ' kn = Some (ConstantDecl {| cst_body := Some v |}).

Lemma tbl_ok_mono Σa Σb tbl : env_ext Σa Σb -> tbl_ok Σa tbl -> tbl_ok Σb tbl.
Proof. intros He H v kn Hin. destruct (H v kn Hin). split; auto. Qed.

Lemma replace_rel Σ' tbl t : tbl_ok Σ' tbl -> lift_rel Σ' t (replace tbl t).
Proof.
  intros Hok. induction t using term_forall_list_ind; rewrite replace_unfold;
    (destruct (liftable _) eqn:Hl;
      [destruct lookup_table eqn:Hlk;
        [apply lookup_table_sound in Hlk; destruct (Hok _ _ Hlk);
         now apply lift_rel_lifted
        | apply lift_rel_refl] |]); cbn.
  all: try (constructor; eauto; fail).
  all: try apply lift_rel_refl.
  all: constructor; eauto.
  all: eapply All_Forall2_map; tea; cbn; intuition eauto.
Qed.

(** [new_decls] as a plain recursion. *)
Fixpoint nd (m : nat) (vs : list term) : list (kername × global_decl) :=
  match vs with
  | [] => []
  | v :: vs => (lift_kn m, ConstantDecl {| cst_body := Some v |}) :: nd (S m) vs
  end.

Lemma new_decls_nd tbl vs : new_decls tbl vs = nd #|tbl| vs.
Proof.
  unfold new_decls, mapi. rewrite -{2}(Nat.add_0_r #|tbl|).
  generalize 0. induction vs; intros k; cbn; auto.
  f_equal. rewrite IHvs. now rewrite Nat.add_succ_r.
Qed.

Lemma register_length tbl vs : #|register tbl vs| = #|tbl| + #|vs|.
Proof. induction vs in tbl |- *; cbn; [lia|]. rewrite IHvs. cbn. lia. Qed.

Lemma register_In tbl vs p : In p (register tbl vs) ->
  In p tbl \/ exists i v, nth_error vs i = Some v /\ p = (v, lift_kn (#|tbl| + i)).
Proof.
  induction vs in tbl |- *; cbn; auto.
  intros [[[= <-]|H]|(i & v & Hn & ->)]%IHvs.
  - right. exists 0, a. split; auto. now rewrite Nat.add_0_r.
  - now left.
  - right. exists (S i), v. split; auto. cbn. now rewrite Nat.add_succ_r.
Qed.

Lemma lookup_nd_in m vs Σx i v : nth_error vs i = Some v ->
  lookup_env (nd m vs ++ Σx) (lift_kn (m + i)) = Some (ConstantDecl {| cst_body := Some v |}).
Proof.
  induction vs in m, i |- *; destruct i; cbn [nd app nth_error]; rewrite ?lookup_env_cons; try discriminate.
  - intros [= ->]. rewrite Nat.add_0_r eqb_refl. reflexivity.
  - intros Hn. destruct (eqb_spec (lift_kn (m + S i)) (lift_kn m)) as [E|E].
    + apply lift_kn_inj in E. lia.
    + rewrite -Nat.add_succ_comm. now apply IHvs.
Qed.

Lemma lookup_nd_out m vs Σx kn :
  (forall i, i < #|vs| -> kn <> lift_kn (m + i)) ->
  lookup_env (nd m vs ++ Σx) kn = lookup_env Σx kn.
Proof.
  induction vs in m |- *; cbn [nd app]; rewrite ?lookup_env_cons; auto. intros H.
  destruct (eqb_spec kn (lift_kn m)) as [E|E].
  - exfalso. apply (H 0); [cbn; lia|]. now rewrite Nat.add_0_r.
  - apply IHvs. intros i Hi. rewrite Nat.add_succ_comm. apply H. cbn; lia.
Qed.

Section Nd.
  Context {efl : EEnvFlags}.
  Variables (Σx : global_declarations) (m : nat).
  Hypothesis Hfr : forall j, m <= j -> lookup_env Σx (lift_kn j) = None.

  Lemma nd_out_lift vs j : m + #|vs| <= j -> lookup_env (nd m vs ++ Σx) (lift_kn j) = None.
  Proof.
    intros Hj. rewrite lookup_nd_out; [|apply Hfr; lia].
    intros i Hi E. apply lift_kn_inj in E. lia.
  Qed.

  Lemma nd_env_ext vs : env_ext Σx (nd m vs ++ Σx).
  Proof.
    intros kn d H. rewrite lookup_nd_out; auto.
    intros i Hi ->. rewrite Hfr in H; [lia|discriminate].
  Qed.

End Nd.

Lemma nd_minductive Σx m vs kn :
  (forall j, m <= j -> lookup_env Σx (lift_kn j) = None) ->
  lookup_minductive (nd m vs ++ Σx) kn = lookup_minductive Σx kn.
Proof.
  intros Hfr. unfold lookup_minductive.
  destruct (lookup_env Σx kn) eqn:E.
  - now rewrite (nd_env_ext Σx m Hfr vs kn g E).
  - induction vs in m, Hfr |- *; cbn [nd app]; rewrite ?lookup_env_cons; [now rewrite E|].
    destruct (eqb_spec kn (lift_kn m)) as [->|]; [now rewrite Hfr in E|].
    apply IHvs. intros j Hj. apply Hfr. lia.
Qed.

Lemma nd_wf {efl : EEnvFlags} Σx m vs :
  (forall j, m <= j -> lookup_env Σx (lift_kn j) = None) ->
  wf_glob Σx -> Forall (fun v => wellformed Σx 0 v /\ is_cvalue v) vs ->
  wf_glob (nd m vs ++ Σx).
Proof.
  induction vs in m |- *; cbn [nd app]; auto. intros Hfr Hwf Hvs. inversion Hvs as [|? ? [Hw Hc] Hvs']; subst.
  constructor.
  - apply IHvs; auto. intros j Hj. apply Hfr. lia.
  - cbn. eapply cvalue_wellformed_transfer; tea.
    intros kn. symmetry. apply nd_minductive. intros j Hj. apply Hfr. lia.
  - apply fresh_global_lookup. rewrite lookup_nd_out; [|apply Hfr; lia].
    intros i Hi E. apply lift_kn_inj in E. lia.
Qed.

Lemma tbl_ok_register Σx tbl vs :
  tbl_ok Σx tbl ->
  (forall j, #|tbl| <= j -> lookup_env Σx (lift_kn j) = None) ->
  Forall (fun v => liftable v) vs ->
  tbl_ok (nd #|tbl| vs ++ Σx) (register tbl vs).
Proof.
  intros Hok Hfr Hl v kn [Hin|(i & v' & Hn & [= -> ->])]%register_In.
  - eapply tbl_ok_mono; tea. now apply nd_env_ext.
  - split.
    + eapply (proj1 (Forall_forall _ _) Hl). now eapply nth_error_In.
    + now apply lookup_nd_in.
Qed.

(** ** (9) Collected values *)

Lemma collect_values_liftable t v : In v (collect_values t) -> liftable v.
Proof.
  induction t using term_forall_list_ind; rewrite collect_values_unfold;
    (match goal with |- context [if liftable ?t then _ else _] => destruct (liftable t) eqn:Hl end; [cbn; intros [<-|[]]; auto|]); cbn; try tauto.
  all: rewrite ?in_app_iff ?in_flat_map; intuition eauto.
  all: match goal with H : exists _, _ |- _ => destruct H as (x & Hx & Hv) end;
    match goal with X : All _ _ |- _ => eapply All_In_inv in X as [X]; tea end;
    cbn in *; intuition eauto.
Qed.

Lemma collect_values_wf {efl : EEnvFlags} Σ t k v :
  wellformed Σ k t -> In v (collect_values t) -> exists k', wellformed Σ k' v.
Proof.
  induction t using term_forall_list_ind in k |- *; rewrite collect_values_unfold;
    (match goal with |- context [if liftable ?t then _ else _] => destruct (liftable t) eqn:Hl end; [cbn; intros ? [<-|[]]; eauto|]); cbn; try tauto.
  all: intros Hw; rtoProp; rewrite ?in_app_iff ?in_flat_map; intros Hin.
  all: try (intuition eauto; fail).
  all: try (destruct Hin as [Hin|Hin]; [now eauto|]).
  all: destruct Hin as (x & Hx & Hv).
  all: try match goal with H : context [if cstr_as_blocks then _ else _] |- _ =>
    destruct cstr_as_blocks; rtoProp; [|destruct args; cbn in *; try discriminate; tauto] end.
  all: match goal with X : All _ _ |- _ => eapply All_In_inv in X as [X]; tea end.
  all: try (unfold wf_fix, wf_fix_gen in *; rtoProp).
  all: repeat match goal with H : is_true (forallb _ _) |- _ => eapply forallb_All in H end.
  all: repeat match goal with H : All _ ?l, Hx : In ?y ?l |- _ => eapply All_In_inv in H as [H]; tea end.
  all: unfold test_def in *; cbn in *; eauto.
Unshelve. all: exact 0.
Qed.

Lemma new_values_incl tbl l v : In v (new_values tbl l) -> In v l.
Proof.
  induction l in tbl |- *; cbn; auto.
  destruct mem_table; [intros H; right; eauto|].
  intros [->|H]; [now left|right; eauto].
Qed.

(** ** (10) [lift_body] and [lift_decl] *)

Lemma lift_body_spec tbl t :
  exists t' vs,
    lift_body tbl t = (t', new_decls tbl vs, register tbl vs) /\
    (forall v, In v vs -> In v (collect_values t)) /\
    (forall Σy, tbl_ok Σy (register tbl vs) -> lift_rel Σy t t').
Proof.
  unfold lift_body. destruct is_cvalue.
  - exists t, []. split; [reflexivity|split]; [intros ? []|intros; apply lift_rel_refl].
  - eexists _, _. split; [reflexivity|]. split.
    + apply new_values_incl.
    + intros. now apply replace_rel.
Qed.

Lemma lift_decl_spec tbl kn d :
  exists d' vs,
    lift_decl tbl kn d = (d', new_decls tbl vs, register tbl vs) /\
    match d with
    | ConstantDecl {| cst_body := Some t |} =>
      (forall v, In v vs -> In v (collect_values t)) /\
      exists t', d' = ConstantDecl {| cst_body := Some t' |} /\
        (forall Σy, tbl_ok Σy (register tbl vs) -> lift_rel Σy t t')
    | _ => d' = d /\ vs = []
    end.
Proof.
  destruct d as [[[t|]]|]; cbn.
  2,3: eexists _, []; split; [reflexivity|auto].
  destruct (liftable t) eqn:Hl.
  - destruct lookup_table eqn:Hlk.
    + exists (ConstantDecl {| cst_body := Some (tConst k) |}), []. split; [reflexivity|].
      split; [cbn; tauto|]. eexists; split; [reflexivity|].
      intros Σy Hok. apply lookup_table_sound in Hlk. destruct (Hok _ _ Hlk).
      now apply lift_rel_lifted.
    + exists (ConstantDecl {| cst_body := Some (tConst (lift_kn #|tbl|)) |}), [t].
      split; [reflexivity|]. split.
      * rewrite collect_values_unfold Hl. auto.
      * eexists; split; [reflexivity|]. intros Σy Hok.
        destruct (Hok t (lift_kn #|tbl|)); [cbn; now left|].
        now apply lift_rel_lifted.
  - destruct (lift_body_spec tbl t) as (t' & vs & -> & Hin & Hr).
    exists (ConstantDecl {| cst_body := Some t' |}), vs. split; [reflexivity|].
    split; auto. eexists; split; [reflexivity|auto].
Qed.


(** ** (11) Invariants of [lift_env] *)

Definition NoLift (Σ : global_declarations) := Forall (fun d => is_lift_kn d.1 = false) Σ.

Lemma NoLift_of Σ : negb (existsb (fun d => is_lift_kn d.1) Σ) -> NoLift Σ.
Proof.
  induction Σ as [|a Σ IH]; cbn; [intros; constructor|].
  rewrite negb_orb. move/andP => [/negbTE H1 H2]. constructor; [exact H1|now apply IH].
Qed.

Lemma lookup_minductive_cons kn' d Σ kn :
  lookup_minductive ((kn', d) :: Σ) kn =
  if eqb kn kn' then (match d with InductiveDecl m => Some m | _ => None end)
  else lookup_minductive Σ kn.
Proof. unfold lookup_minductive. rewrite lookup_env_cons. now destruct eqb. Qed.

Definition cst_rel Σ' (c c' : constant_body) :=
  match cst_body c, cst_body c' with
  | None, None => True
  | Some b, Some b' => lift_rel Σ' b b'
  | _, _ => False
  end.

Lemma cst_rel_mono Σa Σb c c' : env_ext Σa Σb -> cst_rel Σa c c' -> cst_rel Σb c c'.
Proof.
  unfold cst_rel. intros He. destruct (cst_body c), (cst_body c'); auto.
  now apply lift_rel_mono.
Qed.

Record env_inv {efl : EEnvFlags} (Σ Σ1 : global_declarations) (tbl : table) : Prop := {
  inv_tbl : tbl_ok Σ1 tbl;
  inv_fresh : forall j, #|tbl| <= j -> lookup_env Σ1 (lift_kn j) = None;
  inv_ind : forall kn, lookup_minductive Σ kn = lookup_minductive Σ1 kn;
  inv_cst : forall kn c, lookup_env Σ kn = Some (ConstantDecl c) ->
    exists c', lookup_env Σ1 kn = Some (ConstantDecl c') /\ cst_rel Σ1 c c';
  inv_none : forall kn, is_lift_kn kn = false -> lookup_env Σ kn = None -> lookup_env Σ1 kn = None;
  inv_wf : wf_glob Σ1 }.

Lemma cst_presence {efl : EEnvFlags} Σ Σ' :
  (forall kn c, lookup_env Σ kn = Some (ConstantDecl c) ->
    exists c', lookup_env Σ' kn = Some (ConstantDecl c') /\ cst_rel Σ' c c') ->
  forall kn,
    match lookup_constant Σ kn with Some d => has_axioms || isSome d.(cst_body) | _ => false end ->
    match lookup_constant Σ' kn with Some d => has_axioms || isSome d.(cst_body) | _ => false end.
Proof.
  intros H kn. unfold lookup_constant.
  destruct (lookup_env Σ kn) as [[c|]|] eqn:E; try discriminate.
  destruct (H _ _ E) as (c' & -> & Hc). unfold cst_rel in Hc.
  destruct c as [[b|]], c' as [[b'|]]; cbn in *; try easy; rewrite ?orbT; auto.
Qed.

Lemma cst_declared Σ Σ' :
  (forall kn c, lookup_env Σ kn = Some (ConstantDecl c) ->
    exists c', lookup_env Σ' kn = Some (ConstantDecl c') /\ cst_rel Σ' c c') ->
  forall kn b, declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σ' kn {| cst_body := Some b' |} /\ lift_rel Σ' b b'.
Proof.
  unfold declared_constant. intros H kn b E.
  destruct (H _ _ E) as ([[b'|]] & E' & Hc); unfold cst_rel in Hc; cbn in Hc;
    [now exists b'|easy].
Qed.

Section LiftEnv.
  Context {efl : EEnvFlags}.
  Hypothesis HtConst : has_tConst.

  Lemma lift_env_inv Σ : NoLift Σ -> wf_glob Σ -> env_inv Σ (lift_env Σ).1 (lift_env Σ).2.
  Proof.
    induction Σ as [|[kn d] Σ IH]; intros Hnl Hwf.
    { cbn. split; try easy; constructor. }
    apply Forall_cons_iff in Hnl as [Hk HnlΣ].
    depelim Hwf. rename Hwf into HwfΣ. rename H into Hwfd. rename H0 into Hfresh.
    cbn in Hk. specialize (IH HnlΣ HwfΣ).
    cbn [lift_env]. destruct (lift_env Σ) as [Σ1 tbl]. cbn in IH |- *.
    destruct IH as [Hok Hfr Hind Hcst Hnone Hwf1].
    destruct (lift_decl_spec tbl kn d) as (d' & vs & Hld & Hd). rewrite Hld. cbn.
    rewrite new_decls_nd.
    set (Σm := nd #|tbl| vs ++ Σ1).
    have Hext1 : env_ext Σ1 Σm by apply nd_env_ext.
    have Hkn1 : lookup_env Σ1 kn = None by apply Hnone; auto; now apply lookup_fresh_global.
    have Hknm : lookup_env Σm kn = None.
    { unfold Σm. rewrite lookup_nd_out; auto. intros i _. now apply lift_kn_not_orig. }
    have Hext2 : env_ext Σm ((kn, d') :: Σm) by now apply env_ext_cons_fresh.
    have Hindm : forall k, lookup_minductive Σ k = lookup_minductive Σm k.
    { intros k. unfold Σm. rewrite nd_minductive; auto. }
    have Hvs : forall v, In v vs -> [/\ liftable v, wellformed Σ1 0 v & is_cvalue v].
    { intros v Hv. destruct d as [[[t|]]|]; cbn in Hd; try (destruct Hd as [_ ->]; destruct Hv).
      destruct Hd as [Hin _]. apply Hin in Hv.
      have Hl := collect_values_liftable _ _ Hv.
      have Hc := liftable_is_cvalue _ Hl.
      cbn in Hwfd. destruct (collect_values_wf _ _ _ _ Hwfd Hv) as [k' Hw].
      split; auto. eapply cvalue_wellformed_transfer; tea. }
    have Hokm : tbl_ok Σm (register tbl vs).
    { apply tbl_ok_register; auto. apply Forall_forall. intros v Hv. now destruct (Hvs v Hv). }
    have Hcstm : forall k c, lookup_env Σ k = Some (ConstantDecl c) ->
      exists c', lookup_env Σm k = Some (ConstantDecl c') /\ cst_rel Σm c c'.
    { intros k c E. destruct (Hcst _ _ E) as (c' & E' & Hc). exists c'. split; auto.
      now eapply cst_rel_mono. }
    split.
    - eapply tbl_ok_mono; tea.
    - intros j Hj. rewrite register_length in Hj. rewrite lookup_env_cons.
      destruct (eqb_spec (lift_kn j) kn) as [E|_].
      { exfalso. symmetry in E. now apply (lift_kn_not_orig _ _ Hk) in E. }
      unfold Σm. now apply nd_out_lift.
    - intros k. rewrite !lookup_minductive_cons. destruct (eqb_spec k kn) as [->|_]; auto.
      destruct d as [[[t|]]|]; cbn in Hd.
      + now destruct Hd as (_ & t' & -> & _).
      + now destruct Hd as [-> _].
      + now destruct Hd as [-> _].
    - intros k c. rewrite !lookup_env_cons. destruct (eqb_spec k kn) as [->|_].
      + intros [= ->]. destruct c as [[t|]]; cbn in Hd.
        * destruct Hd as (_ & t' & -> & Hr). eexists; split; [reflexivity|]. cbn.
          apply Hr. eapply tbl_ok_mono; tea.
        * destruct Hd as [-> _]. eexists; split; [reflexivity|]. now cbn.
      + intros E. destruct (Hcstm _ _ E) as (c' & E' & Hc). exists c'.
        split; [exact E'|now eapply cst_rel_mono].
    - intros k Hk' E. rewrite lookup_env_cons in E. rewrite lookup_env_cons.
      destruct (eqb_spec k kn); [discriminate|].
      unfold Σm. rewrite lookup_nd_out; [intros i _; now apply lift_kn_not_orig|]. auto.
    - constructor; auto.
      + apply nd_wf; auto. apply Forall_forall. intros v Hv. now destruct (Hvs v Hv).
      + destruct d as [[[t|]]|]; cbn in Hd.
        * destruct Hd as (_ & t' & -> & Hr). cbn in Hwfd |- *.
          eapply wellformed_lift_rel; tea.
          all: first [now apply cst_presence|now apply Hr].
        * now destruct Hd as [-> _].
        * now destruct Hd as [-> _].
      + now apply fresh_global_lookup.
  Qed.
End LiftEnv.

(** ** (12) The main theorems *)

Theorem lift_program_wf {efl : EEnvFlags} p :
  wf_eprogram efl p -> wf_eprogram efl (lift_program efl p).
Proof.
  unfold lift_program. destruct (lift_enabled efl p.1) eqn:He; auto.
  unfold lift_enabled in He. move/andP: He => [/andP [HtC _] Hnl].
  apply NoLift_of in Hnl.
  destruct p as [Σ t]; cbn in *. intros [Hwg Hwt].
  have Hinv := lift_env_inv HtC Σ Hnl Hwg.
  destruct (lift_env Σ) as [Σ1 tbl]. cbn in Hinv.
  destruct Hinv as [Hok Hfr Hind Hcst Hnone Hwf1].
  destruct (lift_body_spec tbl t) as (t' & vs & -> & Hin & Hr). rewrite new_decls_nd.
  have Hindf : forall k, lookup_minductive Σ k = lookup_minductive (nd #|tbl| vs ++ Σ1) k.
  { intros k. rewrite nd_minductive; auto. }
  split; cbn.
  - apply nd_wf; auto. apply Forall_forall. intros v Hv%Hin.
    have Hl := collect_values_liftable _ _ Hv.
    have Hc := liftable_is_cvalue _ Hl.
    destruct (collect_values_wf _ _ _ _ Hwt Hv) as [k' Hw].
    split; auto. eapply cvalue_wellformed_transfer; tea.
  - eapply wellformed_lift_rel; tea.
    + apply cst_presence. intros k c E. destruct (Hcst _ _ E) as (c' & E' & Hc).
      exists c'. split; [now apply nd_env_ext|]. eapply cst_rel_mono; tea. now apply nd_env_ext.
    + apply Hr. apply tbl_ok_register; auto.
      apply Forall_forall. intros v Hv%Hin. now eapply collect_values_liftable.
Qed.

Theorem lift_program_pres {efl : EEnvFlags} {wfl : WcbvFlags} p v :
  wf_eprogram efl p -> eval_eprogram wfl p v ->
  exists v', eval_eprogram wfl (lift_program efl p) v' /\ lift_rel (lift_program efl p).1 v v'.
Proof.
  unfold lift_program. destruct (lift_enabled efl p.1) eqn:He.
  2:{ intros _ Hev. exists v. split; auto. apply lift_rel_refl. }
  unfold lift_enabled in He. move/andP: He => [/andP [HtC _] Hnl].
  apply NoLift_of in Hnl.
  destruct p as [Σ t]; cbn in *. intros [Hwg Hwt] [ev].
  have Hinv := lift_env_inv HtC Σ Hnl Hwg.
  destruct (lift_env Σ) as [Σ1 tbl]. cbn in Hinv.
  destruct Hinv as [Hok Hfr Hind Hcst Hnone Hwf1].
  destruct (lift_body_spec tbl t) as (t' & vs & -> & Hin & Hr). rewrite new_decls_nd. cbn.
  set (Σf := nd #|tbl| vs ++ Σ1).
  have Hindf : forall k, lookup_minductive Σ k = lookup_minductive Σf k.
  { intros k. unfold Σf. rewrite nd_minductive; auto. }
  have Hcstf : forall kn b, declared_constant Σ kn {| cst_body := Some b |} ->
    exists b', declared_constant Σf kn {| cst_body := Some b' |} /\ lift_rel Σf b b'.
  { apply cst_declared. intros k c E. destruct (Hcst _ _ E) as (c' & E' & Hc).
    exists c'. split; [now apply nd_env_ext|]. eapply cst_rel_mono; tea. now apply nd_env_ext. }
  have Hrel : lift_rel Σf t t'.
  { apply Hr. apply tbl_ok_register; auto.
    apply Forall_forall. intros v' Hv%Hin. now eapply collect_values_liftable. }
  have Hsim := lift_rel_simulation Σ Σf Hindf Hcstf t v ev.
  unfold sim_goal in Hsim.
  destruct (Hsim t' Hrel) as (v' & ev' & Hv). now exists v'.
Qed.

(** ** (13) Transform wrapper *)

From MetaRocq.Common Require Import Transform.
Import Transform.

Program Definition lift_constants_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "lifting closed constructor values to constants";
     transform p _ := lift_program efl p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := lift_rel p'.1 v v' |}.
Next Obligation.
  now apply lift_program_wf.
Qed.
Next Obligation.
  now eapply lift_program_pres.
Qed.

(** ** Checks *)

Module LiftConstantsChecks.

  Local Open Scope bs_scope.

  Definition nat_ind : inductive :=
    {| inductive_mind := (MPfile ["Datatypes"], "nat"); inductive_ind := 0 |}.
  Fixpoint lit (n : nat) : term :=
    match n with
    | 0 => tConstruct nat_ind 0 []
    | S n => tConstruct nat_ind 1 [lit n]
    end.
  Definition a : kername := (MPfile ["T"], "a").
  Definition b : kername := (MPfile ["T"], "b").
  Definition cst (t : term) : global_decl := ConstantDecl {| cst_body := Some t |}.

  (* Two occurrences of a literal share one lifted constant. *)
  Example lift_shared :
    (lift_env [(b, cst (tLambda nAnon (lit 2))); (a, cst (tLambda nAnon (lit 2)))]).1
    = [(b, cst (tLambda nAnon (tConst (lift_kn 0))));
       (a, cst (tLambda nAnon (tConst (lift_kn 0))));
       (lift_kn 0, cst (lit 2))].
  Proof. vm_compute. reflexivity. Qed.

  (* A constant whose body is a literal is not used as the shared constant
     (it may be remapped to a foreign value): its body and the later
     occurrences of the literal refer to a lifted constant. *)
  Example lift_literal_body :
    (lift_env [(b, cst (tLambda nAnon (lit 2))); (a, cst (lit 2))]).1
    = [(b, cst (tLambda nAnon (tConst (lift_kn 0))));
       (a, cst (tConst (lift_kn 0)));
       (lift_kn 0, cst (lit 2))].
  Proof. vm_compute. reflexivity. Qed.

End LiftConstantsChecks.
