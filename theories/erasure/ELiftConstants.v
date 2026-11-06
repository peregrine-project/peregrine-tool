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
    [lift_threshold] is itself registered in the table under its own name, so
    later occurrences of that value refer to it directly instead of to a new
    constant; its body is left untouched.  The main term is treated like a
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

    Wellformedness preservation and evaluation preservation are stated as
    axioms, [trust_lift_constants_wf] and [trust_lift_constants_pres], in the
    manner of MetaRocq's [EBeta.trust_betared_wf]/[EInlining] and of the other
    optional Peregrine passes (EInstanceSpecialize.v, ECommonSubexpr.v), and
    so are the two [TransformExt] obligations.  See the documentation of each
    axiom for what it says and why it is believed to hold.  The lemmas before
    the axioms are proved and cover the algebraic core: closed constructor
    values are closed, invariant under lifting and substitution, evaluate to
    themselves ([cvalue_eval_self]), and unfolding a lifted constant gives the
    value back ([eval_tConst_cvalue]); environment lookups of the original
    names go through the inserted declarations ([lookup_env_lift_env]). *)

From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
     ECSubst EReflect EGlobalEnv EProgram EWellformed EWcbvEval.

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

Definition lookup_table (tbl : table) (v : term) : option kername :=
  match find (fun p => eqb p.1 v) tbl with
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
  | tEvar n ts => tEvar n (map (replace tbl) ts)
  | tLambda na b => tLambda na (replace tbl b)
  | tLetIn na v b => tLetIn na (replace tbl v) (replace tbl b)
  | tApp f a => tApp (replace tbl f) (replace tbl a)
  | tCase ci d brs => tCase ci (replace tbl d) (map (fun br => (br.1, replace tbl br.2)) brs)
  | tProj p u => tProj p (replace tbl u)
  | tFix mf idx => tFix (map (map_def (replace tbl)) mf) idx
  | tCoFix mf idx => tCoFix (map (map_def (replace tbl)) mf) idx
  | tConstruct ind c args => tConstruct ind c (map (replace tbl) args)
  | tLazy u => tLazy (replace tbl u)
  | tForce u => tForce (replace tbl u)
  | _ => t
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
        (* The whole body is a liftable value: share it under its own name. *)
        match lookup_table tbl t with
        | Some kn' => (ConstantDecl {| cst_body := Some (tConst kn') |}, [], tbl)
        | None => (d, [], (t, kn) :: tbl)
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
      injection H as <- <- <-; constructor.
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

(** ** (3) Transform wrapper *)

From MetaRocq.Common Require Import Transform.

(** The observational relation: [v'] is [v] in which some closed constructor
    values (necessarily under binders, since the results of evaluation are
    values) have been replaced by references to constants of [Σ'] whose bodies
    are those values. *)
Inductive lift_rel (Σ' : global_declarations) : term -> term -> Prop :=
| lift_rel_lifted t kn n :
    cvalue_size t = Some n ->
    lookup_env Σ' kn = Some (ConstantDecl {| cst_body := Some t |}) ->
    lift_rel Σ' t (tConst kn)
| lift_rel_refl t : lift_rel Σ' t t
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
| lift_rel_lazy u u' : lift_rel Σ' u u' -> lift_rel Σ' (tLazy u) (tLazy u')
| lift_rel_force u u' : lift_rel Σ' u u' -> lift_rel Σ' (tForce u) (tForce u').

(** [trust_lift_constants_wf]: the pass preserves wellformedness.

    Why it holds.  [lift_program] is the identity unless [has_tConst] holds
    and no name of [Σ] lives under [lift_mp].  Otherwise every inserted
    declaration [(lift_kn i, ConstantDecl {| cst_body := Some v |})] has a
    body [v] that is a closed constructor value collected from a wellformed
    body [b] of the declaration [d] just above it; [v] is wellformed under
    the environment below [d] (it mentions no [tRel] and only constructors
    of inductives declared below [d], see [cvalue_closed]), hence under the
    environment at its insertion point, which extends that environment by
    constants only.  Its name is fresh: the indices [i] grow strictly with the
    table, and no original name is under [lift_mp].  The rewritten body
    [replace tbl b] is wellformed because [replace] only substitutes
    [tConst kn] for values, and every [kn] in the table is declared with a
    body below the current declaration ([lookup_env_lift_env] shows the
    original names still resolve).  Inductive declarations are unchanged. *)
Axiom trust_lift_constants_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (lift_program efl input).

(** [trust_lift_constants_pres]: the pass preserves evaluation up to
    [lift_rel].

    Why it holds.  Let [Σ'] be the transformed environment.  Every original
    constant of [Σ] is related to its image by [lift_rel Σ'] (bodies are
    rewritten by [replace], which produces a [lift_rel]-related term because
    every table entry is declared in [Σ'] with the value as its body), and
    [lift_rel Σ'] is closed under [csubst], [substl], [mkApps], [iota_red]
    and [cunfold_fix] since the replaced subterms are closed
    ([cvalue_csubst], [cvalue_lift]).  One then proves by induction on
    [eval Σ t v] that [lift_rel Σ' t t'] implies [eval Σ' t' v'] for some [v']
    with [lift_rel Σ' v v']: the only new case is a replaced value
    [t = v] with [t' = tConst kn], which evaluates by [eval_delta] to the
    body [v], and [v] evaluates to itself ([cvalue_eval_self],
    [eval_tConst_cvalue]); all other cases are congruences, using that the
    related evaluation results are values and therefore never a [tConst], so
    the inversion of [lift_rel] on them is a congruence. *)
Axiom trust_lift_constants_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
    (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (lift_program efl p) v' /\ lift_rel (lift_program efl p).1 v v'.

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
  now apply trust_lift_constants_wf.
Qed.
Next Obligation.
  now eapply trust_lift_constants_pres.
Qed.

Import EProgram EGlobalEnv.

(** The [TransformExt] obligations.  The pass is not compositional with
    respect to [extends] in general (the generated names depend on the whole
    environment), which is also the status of EInstanceSpecialize.v; the
    obligations are axioms as there. *)
#[global]
Axiom lift_constants_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (lift_constants_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).

#[global]
Axiom lift_constants_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (lift_constants_transformation efl wfl)
    extends_eprogram extends_eprogram.
