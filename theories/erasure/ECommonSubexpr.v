(** * Common-subexpression elimination / let-introduction for lambda-box

    This middle-end pass hoists a repeated closed subterm of a constant body
    into a single outermost [tLetIn] and replaces its occurrences by a bound
    variable, so a value that the source shared but erasure duplicated is
    computed once at run time.  Wellformedness preservation and whole-program
    evaluation preservation ([cse_pres_eval]) are proved without axioms.

    Motivation.  Several Peregrine frontends do not preserve [let] bindings:
    Agda inlines its internal let-bindings before erasure, and Lean drops them
    entirely.  A subterm that the source shared through a [let] is therefore
    duplicated in the erased lambda-box term and, under the call-by-value
    semantics of the backends, recomputed once per occurrence at run time.  A
    middle-end CSE pass reverses this for every frontend at once: it hoists a
    repeated subterm into a single [tLetIn] and replaces its occurrences by a
    bound variable, so the work is performed once.

    Why sharing is sound in lambda-box.  Lambda-box is pure (erasure has
    discarded proofs and types; there are no observable effects), so sharing a
    subterm never changes the result.  Under the backends' call-by-value
    evaluation a [tLetIn] forces its bindee exactly once before the body runs,
    which is precisely the sharing wanted.  Sharing does not change strictness
    provided the hoisted subterm already runs on every path: the pass hoists
    only a manifest subterm that the original program evaluates on every
    occurrence, so pulling it out to a [let] that runs once can only remove
    work, never add it, and never moves a diverging computation to a point the
    program did not already demand.

    ---------------------------------------------------------------------------
    ALGORITHM.

    Scope.  The pass runs per constant body.  Constant bodies in a lambda-box
    global environment are closed (no dangling [tRel]).  The pass exploits this:
    it hoists only a subterm [s] that is itself closed ([closedn 0 s]).  A
    closed subterm is invariant under [lift], is identical wherever it appears
    regardless of the number of enclosing binders, and can be substituted by a
    de-Bruijn index that points at a freshly-introduced outermost [let] binder.
    The transform is therefore correct-by-construction with no index arithmetic
    beyond counting the binders descended under.

    Steps, for a closed constant body [t]:
      1. Collect the multiset of all subterms of [t] (fuel-bounded traversal).
      2. Keep the candidates: subterms that are [closedn 0], whose structural
         [size] is at least [cse_threshold] (small subterms are not worth a
         binder, and hoisting a bare [tRel]/[tConst] would be pointless), and
         all of whose occurrences are in strict (always-evaluated) positions.
      3. Keep those occurring at least [cse_min_occ] (= 2) times.
      4. Score each surviving candidate by its estimated dynamic saving,
         [(occurrences - 1) * size], and pick the maximum.
      5. Emit  [tLetIn "cse" best (abstract 0 best t)]  where [abstract k s u]
         replaces every occurrence of [s] in [u] by [tRel k], incrementing [k]
         under each binder so the index always resolves to the outer [let].

    This performs one hoist per constant, capturing the largest repeated
    subterm.  Possible extensions, none of which the pass performs:
      - Hoisting open subterms whose free [tRel]s are all bound above the
        nearest common ancestor of the occurrences, lifted to that ancestor
        with a [lift]; this needs nearest-common-binder-scope analysis.
      - Iterating to a fixpoint and hoisting several candidates simultaneously.
      - Descending into [tPrim] array payloads (treated as a leaf here).

    ---------------------------------------------------------------------------
    PIPELINE PLACEMENT AND VERIFICATION STATUS.

    CSE is the inverse of inlining/beta, so ordering matters: it must run after
    [EInlining]/[EBeta]/dearg, near the end of the unsafe tail, otherwise a
    later beta/inline pass would undo it.  It runs in [extra_unsafe_transforms]
    in erasure/Transforms.v, after [specialize_instances] and before
    [implement_box], which creates no sharing opportunities.  It runs only in
    the untyped pipeline and is off by default in every backend.

    Verification status: fully proved, with no custom axioms.  Wellformedness
    preservation, the algebraic core, and whole-program evaluation preservation
    are all proved.

      - The core algebraic fact is proved: [abstract_subst] shows that for a
        closed [s], [subst [s] k (abstract s k t) = t] whenever [closedn k t] --
        binding [s] and substituting it back reconstructs [t].

      - Wellformedness preservation ([cse_wf]) is fully proved: the pass is
        guarded to fire only when [has_tLetIn] and [has_tRel] hold (otherwise it
        is the identity), the hoisted [s] is a closed, non-lambda subterm of a
        wellformed body hence itself wellformed ([collect_wf],
        [wellformed_closedn_le]), [abstract] preserves wellformedness
        ([wellformed_abstract]), and [wellformed] is invariant under the
        constant-body environment rewrite ([wellformed_cse_env]).
        [Print Assumptions cse_wf] reports no custom axioms.

      - Both [TransformExt] obligations are proved ([extends_cse]).

      - Soundness depends on hoisting only subterms evaluated on every path.
        [candidate_ok] requires every occurrence of the candidate to be in a
        strict (always-evaluated) position
        ([count_term u all_strict = count_term u all_full], via
        [collect_strict]).  This prevents lifting a subterm out of a [tLambda]
        body or an untaken [tCase] branch and forcing it eagerly, which would
        change termination.

      - Evaluation preservation ([cse_pres]) uses the observational relation
        [v' = v]: a sharing pass returns the same value.  It follows from the
        proved theorem [cse_pres_eval], a whole-program CBV simulation between
        [Σ] and [cse_env Σ] (section (3) below).  [Print Assumptions
        cse_transformation] reports only the primitive-type axioms of the
        kernel ([PrimInt63], [PrimFloat], ...), not any CSE-specific axiom. *)

From Stdlib Require Import List Arith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
     EReflect EGlobalEnv EProgram EWellformed EWcbvEval.

Import ListNotations.

(** Tunable parameters. *)
Definition cse_threshold : nat := 8.   (* minimum structural size to hoist *)
Definition cse_min_occ   : nat := 2.   (* minimum occurrence count to hoist *)
Definition cse_name : name := nNamed "cse"%bs.

(** ** Structural size *)
Fixpoint tsize (t : term) : nat :=
  match t with
  | tEvar _ ts => S (list_size tsize ts)
  | tLambda _ b => S (tsize b)
  | tLetIn _ v b => S (tsize v + tsize b)
  | tApp f a => S (tsize f + tsize a)
  | tCase _ d brs => S (tsize d + list_size (fun br => tsize (snd br)) brs)
  | tProj _ u => S (tsize u)
  | tFix mf _ => S (list_size (fun d => tsize (dbody d)) mf)
  | tCoFix mf _ => S (list_size (fun d => tsize (dbody d)) mf)
  | tConstruct _ _ args => S (list_size tsize args)
  | tLazy u => S (tsize u)
  | tForce u => S (tsize u)
  | _ => 1
  end.

(** ** Subterm collection (fuel-bounded, hence trivially terminating) *)
Fixpoint collect (fuel : nat) (t : term) : list term :=
  match fuel with
  | 0 => [t]
  | S fuel =>
      t ::
      match t with
      | tEvar _ ts => flat_map (collect fuel) ts
      | tLambda _ b => collect fuel b
      | tLetIn _ v b => collect fuel v ++ collect fuel b
      | tApp f a => collect fuel f ++ collect fuel a
      | tCase _ d brs =>
          collect fuel d ++ flat_map (fun br => collect fuel (snd br)) brs
      | tProj _ u => collect fuel u
      | tFix mf _ => flat_map (fun d => collect fuel (dbody d)) mf
      | tCoFix mf _ => flat_map (fun d => collect fuel (dbody d)) mf
      | tConstruct _ _ args => flat_map (collect fuel) args
      | tLazy u => collect fuel u
      | tForce u => collect fuel u
      | _ => []
      end
  end.

Definition subterms (t : term) : list term := collect (tsize t) t.

(** ** Strict-position subterm collection.

    Only descends into positions that call-by-value evaluation *always* reaches
    when the whole term is evaluated: both sides of an application, both parts of
    a [tLetIn], the discriminee of a [tCase], the argument of a [tProj]/[tForce],
    and constructor block-arguments.  It deliberately does NOT descend into
    [tLambda] bodies, [tFix]/[tCoFix] bodies, [tCase] branches or [tLazy] bodies
    — those may never run — so every subterm it returns is evaluated whenever the
    enclosing term is.  This is the soundness discriminator for hoisting: a
    closed subterm that runs on every path can be lifted to an outer [let]
    (which forces it once) without changing termination or the result. *)
Fixpoint collect_strict (fuel : nat) (t : term) : list term :=
  match fuel with
  | 0 => [t]
  | S fuel =>
      t ::
      match t with
      | tLetIn _ v b => collect_strict fuel v ++ collect_strict fuel b
      | tApp f a => collect_strict fuel f ++ collect_strict fuel a
      | tCase _ d _ => collect_strict fuel d
      | tProj _ u => collect_strict fuel u
      | tConstruct _ _ args => flat_map (collect_strict fuel) args
      | tForce u => collect_strict fuel u
      | _ => []
      end
  end.

Definition subterms_strict (t : term) : list term := collect_strict (tsize t) t.

(** ** Occurrence counting and de-duplication over the boolean [eqb] on terms *)
Definition count_term (x : term) (l : list term) : nat :=
  List.length (List.filter (fun y => eqb x y) l).

Definition mem_term (x : term) (l : list term) : bool :=
  List.existsb (fun y => eqb x y) l.

Definition dedup_terms (l : list term) : list term :=
  List.fold_right (fun x acc => if mem_term x acc then acc else x :: acc) [] l.

(** ** Abstraction: replace every occurrence of [s] by [tRel k], deepening [k]
       under binders.  [s] is a *closed* subterm, so it is textually identical
       at every depth and no lifting of [s] is required. *)
Fixpoint abstract (s : term) (k : nat) (t : term) {struct t} : term :=
  if eqb s t then tRel k
  else
    match t with
    | tEvar n ts => tEvar n (map (abstract s k) ts)
    | tLambda na b => tLambda na (abstract s (S k) b)
    | tLetIn na v b => tLetIn na (abstract s k v) (abstract s (S k) b)
    | tApp f a => tApp (abstract s k f) (abstract s k a)
    | tCase ci d brs =>
        tCase ci (abstract s k d)
          (map (fun br => (fst br, abstract s (k + List.length (fst br)) (snd br))) brs)
    | tProj p u => tProj p (abstract s k u)
    | tFix mf i =>
        tFix (map (map_def (abstract s (k + List.length mf))) mf) i
    | tCoFix mf i =>
        tCoFix (map (map_def (abstract s (k + List.length mf))) mf) i
    | tConstruct ind n args => tConstruct ind n (map (abstract s k) args)
    | tLazy u => tLazy (abstract s k u)
    | tForce u => tForce (abstract s k u)
    | tPrim p => tPrim p
    | tRel _ | tVar _ | tConst _ | tBox => t
    end.

(** ** Candidate selection: the closed, large-enough, repeated subterm with the
       greatest estimated dynamic saving. *)
(** A subterm is a valid hoisting candidate when it is closed, not a lambda,
    big enough, occurs at least [cse_min_occ] times in *strict* positions, and
    — crucially for soundness — has NO occurrence in a non-strict position
    (its count over the strict subterms equals its count over all subterms).
    The last conjunct is what guarantees the hoisted subterm is evaluated on
    every path, so lifting it to an eager outer [let] preserves semantics. *)
Definition candidate_ok (all_strict all_full : list term) (u : term) : bool :=
  closedn 0 u && negb (isLambda u)
  && (cse_threshold <=? tsize u)
  && (cse_min_occ <=? count_term u all_strict)
  && (count_term u all_strict =? count_term u all_full).

Definition saving (all : list term) (u : term) : nat :=
  (count_term u all - 1) * tsize u.

(* argmax of [saving] over a candidate list; [None] if empty *)
Definition best_candidate (all : list term) (cands : list term) : option term :=
  List.fold_right
    (fun u acc =>
       match acc with
       | None => Some u
       | Some v => if saving all v <? saving all u then Some u else acc
       end)
    None cands.

(** ** Enabling guard.

    Hoisting emits a [tLetIn] whose body contains a fresh [tRel].  Those two
    node kinds must be permitted by the target [EEnvFlags], otherwise the emitted
    term is not [wellformed].  The pass therefore fires only when both
    [has_tLetIn] and [has_tRel] are set; when they are not, [cse_term] is the
    identity and the transform is trivially wellformedness- and
    semantics-preserving.  (In the intended pipeline slot both flags hold.) *)
Definition cse_enabled (efl : EEnvFlags) : bool := has_tLetIn && has_tRel.

(** ** The per-term transform: one hoist. *)
Definition cse_term (efl : EEnvFlags) (t : term) : term :=
  if cse_enabled efl then
    let all_strict := subterms_strict t in
    let all_full := subterms t in
    let cands := dedup_terms (List.filter (candidate_ok all_strict all_full) all_strict) in
    match best_candidate all_strict cands with
    | None => t
    | Some s => tLetIn cse_name s (abstract s 0 t)
    end
  else t.

(** ** Lifting to constant bodies / environments / programs *)
Definition cse_in_constant_body (efl : EEnvFlags) (cst : constant_body)
  : constant_body :=
  {| cst_body := option_map (cse_term efl) (cst_body cst) |}.

Definition cse_in_decl (efl : EEnvFlags) (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cst => ConstantDecl (cse_in_constant_body efl cst)
  | _ => d
  end.

Definition cse_env (efl : EEnvFlags) (Σ : global_declarations)
  : global_declarations :=
  map (fun '(kn, decl) => (kn, cse_in_decl efl decl)) Σ.

Definition cse_program (efl : EEnvFlags) (p : program) : program :=
  (cse_env efl p.1, cse_term efl p.2).

(** * VERIFICATION *)

(** ** (1) [abstract] is a left inverse of substitution.

    If [s] is closed and [t] is closed up to [k], then substituting [s] back for
    the fresh de-Bruijn index [k] undoes [abstract s k].  This is the algebraic
    heart of the transform: it is exactly the fact that makes
    [tLetIn "cse" s (abstract s 0 t)] reconstruct [t]. *)

Lemma subst_rel_closed s k : closedn 0 s -> subst [s] k (tRel k) = s.
Proof.
  intros Hs. simpl. rewrite Nat.leb_refl, Nat.sub_diag. simpl.
  now apply lift_closed.
Qed.

Lemma abstract_subst s (Hs : closedn 0 s) :
  forall t k, closedn k t -> subst [s] k (abstract s k t) = t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k Hcl; cbn [abstract];
    (match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [Heq|Hne] end);
    try (rewrite <- Heq; simpl subst; rewrite Nat.leb_refl, Nat.sub_diag; simpl;
         now apply lift_closed).
  all: cbn in Hcl |- *; rtoProp.
  - (* tBox *) reflexivity.
  - (* tRel *) destruct (Nat.leb_spec k n);
      [ apply Nat.ltb_lt in Hcl; exfalso; lia | reflexivity ].
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite map_map. apply All_map_id.
    solve_all.
  - (* tLambda *) f_equal. now apply IHt.
  - (* tLetIn *) f_equal; [ now apply IHt1 | now apply IHt2 ].
  - (* tApp *) f_equal; [ now apply IHt1 | now apply IHt2 ].
  - (* tConst *) reflexivity.
  - (* tConstruct *) f_equal. rewrite map_map. apply All_map_id. solve_all.
  - (* tCase *) f_equal.
    + now apply IHt.
    + rewrite map_map. apply All_map_id.
      apply forallb_All in H0. solve_all.
      destruct x as [nas br]; cbn in *. f_equal.
      rewrite (Nat.add_comm k #|nas|). apply a. exact b.
  - (* tProj *) f_equal. now apply IHt.
  - (* tFix *) f_equal. rewrite ?length_map, map_map. apply All_map_id.
    apply forallb_All in Hcl. solve_all.
    unfold map_def; destruct x as [dn db ra]; cbn in *. f_equal.
    unfold test_def in *; cbn in *. rewrite (Nat.add_comm k #|m|). apply a. exact b.
  - (* tCoFix *) f_equal. rewrite ?length_map, map_map. apply All_map_id.
    apply forallb_All in Hcl. solve_all.
    unfold map_def; destruct x as [dn db ra]; cbn in *. f_equal.
    unfold test_def in *; cbn in *. rewrite (Nat.add_comm k #|m|). apply a. exact b.
  - (* tPrim *) change (subst [s] k (tPrim p) = tPrim p).
    apply subst_closed. exact Hcl.
  - (* tLazy *) f_equal. now apply IHt.
  - (* tForce *) f_equal. now apply IHt.
Qed.

(** ** (2a) [abstract] never turns a lambda into a non-lambda, provided the
       hoisted subterm [s] is itself not a lambda.  This is what keeps the
       "fixpoint bodies are lambdas" wellformedness invariant. *)
Lemma abstract_isLambda s k t :
  isLambda s = false -> isLambda t = true -> isLambda (abstract s k t) = true.
Proof.
  destruct t; simpl; intros Hs Ht; try discriminate.
  match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [->|_] end;
    [ simpl in Hs; discriminate | reflexivity ].
Qed.

(** ** (2b) [abstract] preserves wellformedness.

    Replacing a (non-lambda) closed subterm [s] by a fresh de-Bruijn index
    keeps the term wellformed: it introduces only a [tRel] (needing [has_tRel]),
    never a new [tConst]/[tConstruct]/[tCase]/[tProj]/[tFix]/[tCoFix] head, so
    all environment lookups and structural checks are preserved. *)
Lemma wellformed_abstract {efl : EEnvFlags} (Σ : global_declarations) s
  (Hrel : has_tRel) (Hnl : isLambda s = false) :
  forall t k, wellformed Σ k t -> wellformed Σ (S k) (abstract s k t).
Proof.
  intros t; induction t using term_forall_list_ind; intros k Hwf; cbn [abstract];
    (match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [Heq|Hne] end);
    try (cbn; apply andb_true_intro; split; [ exact Hrel | apply Nat.leb_le; lia ]).
  all: cbn in Hwf |- *.
  - (* tBox *) assumption.
  - (* tRel *) apply andb_and in Hwf as [Hr Hlt]. rewrite Hr. cbn.
    apply Nat.leb_le. apply Nat.ltb_lt in Hlt. lia.
  - (* tVar *) assumption.
  - (* tEvar *) apply andb_and in Hwf as [Hf Hl]. rewrite Hf. cbn.
    apply forallb_All in Hl. solve_all.
  - (* tLambda *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    now apply IHt.
  - (* tLetIn *) apply andb_and in Hwf as [Hfb Hb2]. apply andb_and in Hfb as [Hf Hb1].
    rewrite Hf. cbn. apply andb_true_intro; split; [ now apply IHt1 | now apply IHt2 ].
  - (* tApp *) apply andb_and in Hwf as [Hfb Hb2]. apply andb_and in Hfb as [Hf Hb1].
    rewrite Hf. cbn. apply andb_true_intro; split; [ now apply IHt1 | now apply IHt2 ].
  - (* tConst *) assumption.
  - (* tConstruct *) apply andb_and in Hwf as [Hfl Hrest].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    destruct cstr_as_blocks.
    + apply andb_and in Hrest as [Hc Hargs]. rewrite length_map.
      apply andb_true_intro; split; [ assumption | ].
      apply forallb_All in Hargs. apply All_forallb. apply All_map. solve_all.
    + now destruct args.
  - (* tCase *) apply andb_and in Hwf as [Hf Hr1].
    apply andb_and in Hr1 as [Hr2 Hbrs]. apply andb_and in Hr2 as [Hbr Hc].
    rewrite Hf. cbn. rewrite length_map.
    apply andb_true_intro; split; [ apply andb_true_intro; split | ].
    + assumption.
    + now apply IHt.
    + apply forallb_All in Hbrs. apply All_forallb. apply All_map. solve_all.
      destruct x as [nas br]; cbn in *. rewrite Nat.add_succ_r.
      rewrite (Nat.add_comm k #|nas|). apply a. exact b.
  - (* tProj *) apply andb_and in Hwf as [Hfl Hc].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn. now apply IHt.
  - (* tFix *) apply andb_and in Hwf as [Hfl Hfix].
    apply andb_and in Hfl as [Hf Hlam]. rewrite Hf. cbn.
    apply andb_true_intro; split.
    + apply forallb_All in Hlam. apply All_forallb. apply All_map. solve_all.
      destruct x as [dn db ra]; cbn in *. now apply abstract_isLambda.
    + unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
      rewrite ?length_map. apply andb_true_intro; split; [ assumption | ].
      apply forallb_All in Hbods. apply All_forallb. apply All_map. solve_all.
      unfold test_def in *. destruct x as [dn db ra]; cbn in *.
      rewrite Nat.add_succ_r. rewrite (Nat.add_comm k #|m|). apply a; assumption.
  - (* tCoFix *) apply andb_and in Hwf as [Hf Hfix]. rewrite Hf. cbn.
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    rewrite ?length_map. apply andb_true_intro; split; [ assumption | ].
    apply forallb_All in Hbods. apply All_forallb. apply All_map. solve_all.
    unfold test_def in *. destruct x as [dn db ra]; cbn in *.
    rewrite Nat.add_succ_r. rewrite (Nat.add_comm k #|m|). apply a; assumption.
  - (* tPrim *) change (wellformed Σ (S k) (tPrim p)).
    eapply wellformed_up; [ exact Hwf | lia ].
  - (* tLazy *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn. now apply IHt.
  - (* tForce *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn. now apply IHt.
Qed.

(** ** (2c) Wellformedness relaxes the de-Bruijn bound down to any closedness
       level actually met by the term. *)
Lemma wellformed_closedn_le {efl : EEnvFlags} (Σ : global_declarations) :
  forall t k k', wellformed Σ k t -> closedn k' t -> wellformed Σ k' t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k k' Hwf Hcl;
    cbn in Hwf, Hcl |- *; try assumption.
  - (* tRel *) apply andb_and in Hwf as [Hr _]. now rewrite Hr, Hcl.
  - (* tEvar *) apply andb_and in Hwf as [Hf Hl]. rewrite Hf. cbn.
    apply forallb_All in Hl. apply forallb_All in Hcl. solve_all.
  - (* tLambda *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
  - (* tLetIn *) apply andb_and in Hwf as [Hfb Hb2].
    apply andb_and in Hfb as [Hf Hb1]. apply andb_and in Hcl as [Hc1 Hc2].
    rewrite Hf. cbn. apply andb_true_intro; split;
      [ eapply IHt1; eassumption | eapply IHt2; eassumption ].
  - (* tApp *) apply andb_and in Hwf as [Hfb Hb2].
    apply andb_and in Hfb as [Hf Hb1]. apply andb_and in Hcl as [Hc1 Hc2].
    rewrite Hf. cbn. apply andb_true_intro; split;
      [ eapply IHt1; eassumption | eapply IHt2; eassumption ].
  - (* tConstruct *) apply andb_and in Hwf as [Hfl Hrest].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    destruct cstr_as_blocks.
    + apply andb_and in Hrest as [Hc Hargs]. apply andb_true_intro; split;
        [ assumption | ]. apply forallb_All in Hargs. apply forallb_All in Hcl.
      apply All_forallb. solve_all.
    + assumption.
  - (* tCase *) apply andb_and in Hwf as [Hf Hr1].
    apply andb_and in Hr1 as [Hr2 Hbrs]. apply andb_and in Hr2 as [Hbr Hc].
    apply andb_and in Hcl as [Hcd Hcbrs]. rewrite Hf. cbn. rewrite Hbr. cbn.
    apply andb_true_intro; split.
    + eapply IHt; eassumption.
    + apply forallb_All in Hbrs. apply forallb_All in Hcbrs.
      apply All_forallb. solve_all.
  - (* tProj *) apply andb_and in Hwf as [Hfl Hc].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    eapply IHt; eassumption.
  - (* tFix *) apply andb_and in Hwf as [Hfl Hfix].
    apply andb_and in Hfl as [Hf Hlam]. rewrite Hf. cbn.
    apply andb_true_intro; split; [ exact Hlam | ].
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    apply andb_true_intro; split; [ assumption | ].
    unfold test_def in *. apply forallb_All in Hbods. apply forallb_All in Hcl.
    apply All_forallb. solve_all.
  - (* tCoFix *) apply andb_and in Hwf as [Hf Hfix]. rewrite Hf. cbn.
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    apply andb_true_intro; split; [ assumption | ].
    unfold test_def in *. apply forallb_All in Hbods. apply forallb_All in Hcl.
    apply All_forallb. solve_all.
  - (* tPrim *) apply andb_and in Hwf as [Hp Hwp]. rewrite Hp. cbn.
    destruct p as [tag pm]; destruct pm; cbn in *; try reflexivity.
    inversion X; subst. destruct X0 as [Hdef Hvals].
    unfold test_array_model in *. apply andb_and in Hwp as [Hwd Hwv].
    apply andb_and in Hcl as [Hcd Hcv]. apply andb_true_intro; split.
    { eapply Hdef; eassumption. }
    apply forallb_All in Hwv. apply forallb_All in Hcv. apply All_forallb. solve_all.
  - (* tLazy *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
  - (* tForce *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
Qed.

(** ** (2d) Every subterm collected by [collect] out of a wellformed term is
       itself wellformed (at some de-Bruijn level). *)
Lemma collect_wf {efl : EEnvFlags} (Σ : global_declarations) :
  forall fuel t k u,
  wellformed Σ k t -> In u (collect fuel t) -> exists m, wellformed Σ m u.
Proof.
  induction fuel as [|fuel IHfuel]; intros t k u Hwf Hin.
  - cbn in Hin. destruct Hin as [<-|[]]. now exists k.
  - cbn in Hin. destruct Hin as [<-|Hin]; [ now exists k | ].
    destruct t; cbn in Hwf, Hin; try solve [ destruct Hin ].
    + (* tEvar *) apply andb_and in Hwf as [_ Hfb].
      apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hfb x Hxl).
    + (* tLambda *) apply andb_and in Hwf as [_ Hb].
      eapply IHfuel; [ exact Hb | exact Hin ].
    + (* tLetIn *) apply andb_and in Hwf as [Hf1 Hb2].
      apply andb_and in Hf1 as [_ Hb1]. apply in_app_or in Hin as [Hin|Hin];
        [ eapply IHfuel; [ exact Hb1 | exact Hin ]
        | eapply IHfuel; [ exact Hb2 | exact Hin ] ].
    + (* tApp *) apply andb_and in Hwf as [Hf1 Hb2].
      apply andb_and in Hf1 as [_ Hb1]. apply in_app_or in Hin as [Hin|Hin];
        [ eapply IHfuel; [ exact Hb1 | exact Hin ]
        | eapply IHfuel; [ exact Hb2 | exact Hin ] ].
    + (* tConstruct *) apply andb_and in Hwf as [_ Hrest]. destruct cstr_as_blocks.
      * apply andb_and in Hrest as [_ Hfb]. apply in_flat_map in Hin as [x [Hxl Hux]].
        eapply IHfuel; [ | exact Hux ]. exact (proj1 (forallb_forall _ _) Hfb x Hxl).
      * destruct args; [ destruct Hin | discriminate ].
    + (* tCase *) apply andb_and in Hwf as [_ Hr1].
      apply andb_and in Hr1 as [Hr2 Hfb]. apply andb_and in Hr2 as [_ Hc].
      apply in_app_or in Hin as [Hin|Hin].
      * eapply IHfuel; [ exact Hc | exact Hin ].
      * apply in_flat_map in Hin as [x [Hxl Hux]].
        eapply IHfuel; [ | exact Hux ].
        exact (proj1 (forallb_forall _ _) Hfb x Hxl).
    + (* tProj *) apply andb_and in Hwf as [_ Hc].
      eapply IHfuel; [ exact Hc | exact Hin ].
    + (* tFix *) apply andb_and in Hwf as [_ Hfix]. unfold wf_fix_gen in Hfix.
      apply andb_and in Hfix as [_ Hbods]. apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hbods x Hxl).
    + (* tCoFix *) apply andb_and in Hwf as [_ Hfix]. unfold wf_fix_gen in Hfix.
      apply andb_and in Hfix as [_ Hbods]. apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hbods x Hxl).
    + (* tLazy *) apply andb_and in Hwf as [_ Hb]. eapply IHfuel; [ exact Hb | exact Hin ].
    + (* tForce *) apply andb_and in Hwf as [_ Hb]. eapply IHfuel; [ exact Hb | exact Hin ].
Qed.

(** A hoisted candidate (a closed subterm of a wellformed body) is wellformed
    at level 0. *)
Lemma cse_subterm_wf {efl : EEnvFlags} (Σ : global_declarations) t s :
  wellformed Σ 0 t -> In s (subterms t) -> closedn 0 s -> wellformed Σ 0 s.
Proof.
  intros Hwf Hin Hcl. unfold subterms in Hin.
  eapply collect_wf in Hin as [m Hm]; [ | exact Hwf ].
  eapply wellformed_closedn_le; eassumption.
Qed.

(** Strict-position subterms are genuine subterms. *)
Lemma collect_strict_incl : forall fuel t u,
  In u (collect_strict fuel t) -> In u (collect fuel t).
Proof.
  induction fuel as [|fuel IH]; intros t u Hin; [ exact Hin | ].
  cbn in Hin |- *. destruct Hin as [->|Hin]; [ now left | right ].
  destruct t; cbn in Hin |- *; try solve [ destruct Hin ].
  - (* tLetIn *) apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [ left; now apply IH | right; now apply IH ].
  - (* tApp *) apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [ left; now apply IH | right; now apply IH ].
  - (* tConstruct *) apply in_flat_map in Hin as [x [Hx Hu]].
    apply in_flat_map. exists x. split; [ exact Hx | now apply IH ].
  - (* tCase *) apply in_or_app. left. now apply IH.
  - (* tProj *) now apply IH.
  - (* tForce *) now apply IH.
Qed.

Lemma subterms_strict_incl t u : In u (subterms_strict t) -> In u (subterms t).
Proof. apply collect_strict_incl. Qed.

(** ** (2e) [cse_env] keeps every key and inductive declaration and only
       rewrites constant bodies, so all environment lookups are preserved and
       [wellformed] is invariant under it. *)

Lemma lookup_env_cse efl Σ kn :
  lookup_env (cse_env efl Σ) kn = option_map (cse_in_decl efl) (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; [ reflexivity | ].
  destruct (eq_kername kn kn'); cbn; [ reflexivity | exact IH ].
Qed.

Lemma lookup_minductive_cse efl Σ kn :
  lookup_minductive (cse_env efl Σ) kn = lookup_minductive Σ kn.
Proof.
  unfold lookup_minductive. rewrite lookup_env_cse.
  destruct (lookup_env Σ kn) as [[]|]; reflexivity.
Qed.

Lemma lookup_inductive_cse efl Σ kn :
  lookup_inductive (cse_env efl Σ) kn = lookup_inductive Σ kn.
Proof. unfold lookup_inductive. now rewrite lookup_minductive_cse. Qed.

Lemma lookup_constructor_cse efl Σ kn c :
  lookup_constructor (cse_env efl Σ) kn c = lookup_constructor Σ kn c.
Proof. unfold lookup_constructor. now rewrite lookup_inductive_cse. Qed.

Lemma lookup_constructor_pars_args_cse efl Σ kn c :
  lookup_constructor_pars_args (cse_env efl Σ) kn c
  = lookup_constructor_pars_args Σ kn c.
Proof. unfold lookup_constructor_pars_args. now rewrite lookup_constructor_cse. Qed.

Lemma lookup_projection_cse efl Σ p :
  lookup_projection (cse_env efl Σ) p = lookup_projection Σ p.
Proof. unfold lookup_projection. now rewrite lookup_constructor_cse. Qed.

Lemma lookup_constant_cse efl Σ kn :
  lookup_constant (cse_env efl Σ) kn
  = option_map (cse_in_constant_body efl) (lookup_constant Σ kn).
Proof.
  unfold lookup_constant. rewrite lookup_env_cse.
  destruct (lookup_env Σ kn) as [[]|]; reflexivity.
Qed.

Lemma wellformed_cse_env efl Σ :
  forall t k, wellformed (cse_env efl Σ) k t = wellformed Σ k t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k;
    cbn -[lookup_constant lookup_inductive lookup_constructor
          lookup_constructor_pars_args lookup_projection]; auto.
  - (* tEvar *) f_equal. eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tLambda *) now rewrite IHt.
  - (* tLetIn *) now rewrite IHt1, IHt2.
  - (* tApp *) now rewrite IHt1, IHt2.
  - (* tConst *) rewrite lookup_constant_cse.
    destruct (lookup_constant Σ s) as [c|]; cbn; [ | reflexivity ].
    destruct (cst_body c); reflexivity.
  - (* tConstruct *) rewrite lookup_constructor_cse.
    destruct cstr_as_blocks; [ | reflexivity ].
    rewrite lookup_constructor_pars_args_cse. f_equal. f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tCase *) unfold wf_brs. rewrite lookup_inductive_cse.
    rewrite IHt. do 2 f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. now rewrite Hx.
  - (* tProj *) rewrite lookup_projection_cse. now rewrite IHt.
  - (* tFix *) unfold wf_fix_gen. do 2 f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. unfold test_def. now rewrite Hx.
  - (* tCoFix *) unfold wf_fix_gen. f_equal. f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. unfold test_def. now rewrite Hx.
  - (* tPrim *) f_equal. destruct p as [tag pm]; destruct pm; cbn; auto.
    unfold test_array_model. inversion X; subst. destruct X0 as [Hdef Hvals].
    rewrite Hdef. f_equal. eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tLazy *) now rewrite IHt.
  - (* tForce *) now rewrite IHt.
Qed.

(** ** (2f) The hoisted candidate is a genuine, closed, non-lambda subterm. *)

Lemma best_candidate_In all cands s :
  best_candidate all cands = Some s -> In s cands.
Proof.
  unfold best_candidate. induction cands as [|c cands IH]; [ discriminate | ].
  simpl fold_right. destruct (fold_right _ _ cands) as [v|] eqn:E.
  - destruct (saving all v <? saving all c).
    + intros Heq; inversion Heq; subst. now left.
    + intros Heq; inversion Heq; subst. right. now apply IH.
  - intros Heq; inversion Heq; subst. now left.
Qed.

Lemma dedup_In x l : In x (dedup_terms l) -> In x l.
Proof.
  induction l as [|a l IH]; simpl; [ auto | ].
  destruct (mem_term a (dedup_terms l)).
  - intros H. apply in_cons. now apply IH.
  - intros [->|H]; [ apply in_eq | apply in_cons; now apply IH ].
Qed.

(** ** (2g) [cse_term] preserves wellformedness at level 0. *)
Lemma cse_term_wf (efl : EEnvFlags) (Σ : global_declarations) t :
  wellformed Σ 0 t -> wellformed Σ 0 (cse_term efl t).
Proof.
  intros Hwf. unfold cse_term.
  destruct (cse_enabled efl) eqn:Hen; [ | exact Hwf ].
  destruct (best_candidate _ _) as [s|] eqn:Hbest; [ | exact Hwf ].
  unfold cse_enabled in Hen. apply andb_and in Hen as [Hlet Hrel].
  apply best_candidate_In in Hbest. apply dedup_In in Hbest.
  apply filter_In in Hbest as [Hin Hok].
  apply subterms_strict_incl in Hin.
  unfold candidate_ok in Hok.
  apply andb_and in Hok as [Hok _]. apply andb_and in Hok as [Hok _].
  apply andb_and in Hok as [Hok _]. apply andb_and in Hok as [Hcl Hnl].
  apply negb_true_iff in Hnl.
  cbn. rewrite Hlet. cbn. apply andb_true_intro; split.
  - eapply cse_subterm_wf; eassumption.
  - now apply wellformed_abstract.
Qed.

(** ** (2h) Key preservation for the environment transformation. *)
Lemma fresh_global_cse efl kn Σ :
  fresh_global kn Σ -> fresh_global kn (cse_env efl Σ).
Proof.
  unfold fresh_global. intros H. apply Forall_forall. intros x Hx.
  unfold cse_env in Hx. apply in_map_iff in Hx as [[kn' d] [Heq Hin]].
  subst x. cbn. eapply Forall_forall in H; [ | exact Hin ]. exact H.
Qed.

Lemma cse_env_cons efl kn d Σ :
  cse_env efl ((kn, d) :: Σ) = (kn, cse_in_decl efl d) :: cse_env efl Σ.
Proof. reflexivity. Qed.

Lemma cse_env_wf efl Σ : wf_glob Σ -> wf_glob (cse_env efl Σ).
Proof.
  induction 1 as [| kn d Σ Hg IH Hdecl Hfresh]; [ constructor | ].
  rewrite cse_env_cons. constructor; [ exact IH | | now apply fresh_global_cse ].
  destruct d as [c|m].
  - unfold wf_global_decl, cse_in_decl, cse_in_constant_body in *;
      cbn [cst_body] in *.
    destruct (cst_body c) as [b|] eqn:Ecb; cbn [option_map option_default] in *.
    + rewrite wellformed_cse_env. now apply cse_term_wf.
    + exact Hdecl.
  - exact Hdecl.
Qed.

(** ** (2) MAIN WELLFORMEDNESS PRESERVATION. *)
Lemma cse_wf (efl : EEnvFlags) (p : eprogram) :
  wf_eprogram efl p -> wf_eprogram efl (cse_program efl p).
Proof.
  intros [Hglob Hmain]. split.
  - now apply cse_env_wf.
  - cbn. rewrite wellformed_cse_env. now apply cse_term_wf.
Qed.

(** ** Transform wrapper ([Compatible]-class), mirroring EInstanceSpecialize.v
       and MetaRocq's EBeta.v. *)

From MetaRocq.Common Require Import Transform.

(** ** (3) SEMANTICS PRESERVATION.

    CORRECTNESS MODEL.

    The observational relation for a sharing pass is the identity on values,
    [v' = v]: hoisting a closed subterm evaluated on every path, forcing it once
    in an outer [let], and substituting its value back yields the same value.
    (The congruence-style obseq [v' = cse_term v] used by [EBeta] does not apply
    here: [cse_term] performs one global hoist, so it is not a congruence and
    does not commute with evaluation — for a value with a repeated closed
    subterm, [cse_term v] is a [tLetIn], which cannot evaluate to itself.)  The
    algebraic backbone is proved: [abstract_subst] gives
    [subst0 s (abstract s 0 t) = t] for closed [s]; under [eval_zeta] the [let]
    forces [s] to [s'] and [csubst]s it back, and [closed_subst] turns that
    [csubst] into the [subst] of [abstract_subst].

    SOUNDNESS DISCRIMINATOR.  Hoisting is sound only for subterms evaluated on
    every path.  [candidate_ok] enforces this: a candidate must have all its
    occurrences in strict (always-evaluated) positions
    ([count_term u all_strict = count_term u all_full]).  Without this guard the
    pass would be unsound — it could lift a subterm out of a [tLambda] body or
    an untaken [tCase] branch and force it eagerly, changing termination.

    PROOF OF [cse_pres_eval].  The strict positions ([collect_strict]) are
    exactly the positions every applicable [EWcbvEval] rule evaluates before
    producing a value: both sides of [tLetIn] and [tApp], the [tCase] and
    [tProj] scrutinee, [tConstruct] arguments and the [tForce] argument.  Under
    binders, [tCase] branches, [tFix]/[tCoFix] bodies, [tLazy] and [tPrim]
    payloads nothing is hoisted.  The proof has three parts.
      (3a) Counting.  Equal strict and full occurrence counts give
           [strict_only s t] ([count_eq_strict_only]): [abstract s] is the
           identity away from strict positions.  Every strict occurrence is a
           [strict_sub] of [t] ([collect_strict_sub]).
      (3b) Environment.  [cse_env] keeps every inductive declaration and every
           constant name, so all lookups used by evaluation agree ([*_cse]).
      (3c) Simulation.  [cse_rel t t'] says that [t'] is [t] with some closed
           strict subterms replaced by their values (holes).  Induction over
           [eval Σ t v] shows that
             (i) every [t'] with [cse_rel t t'] evaluates to the same [v] under
                 [Σ'], and
             (ii) every closed strict subterm of [t] evaluates under [Σ] (with
                 the IH available for it) ([cse_sim]).
           [cse_term_sim] then handles [cse_term] itself: [let x := s in
           abstract s 0 t] forces [s] to [sv] by (ii), and
           [csubst sv 0 (abstract s 0 t)] is [cse_rel]-related to [t]
           ([abstract_rel]).  The delta rule uses [cse_term_sim] for the
           rewritten constant body.
    The conclusion of [cse_pres_eval] is squashed ([∥ _ ∥]) because the
    simulation is proved in [Prop].  This is enough for [eval_eprogram], which
    is squashed as well.  Holes are evaluated values, so they are closed
    values that evaluate to themselves under both environments.  This is why
    replacing [s] by [sv] does not change the result even when [sv] is a
    [tLambda]/[tFix] closure: the value [v] is produced by the same rule
    instance and is syntactically identical. *)

From Stdlib Require Import Lia.
From MetaRocq.Erasure Require Import ECSubst.
From Equations Require Import Equations.

(** *** (3a) Occurrence counting: equal strict and full counts mean that every
    occurrence of the candidate is in a strict position. *)

Lemma tsize_pos t : 0 < tsize t.
Proof. destruct t; cbn; lia. Qed.

Lemma In_list_size_le {A} (f : A -> nat) x l : In x l -> f x <= list_size f l.
Proof.
  induction l as [|a l IH]; cbn; [ intros [] | ].
  intros [->|H]; [ lia | specialize (IH H); lia ].
Qed.

Lemma count_term_cons x y l :
  count_term x (y :: l) = (if eqb x y then 1 else 0) + count_term x l.
Proof. unfold count_term. cbn. destruct (eqb x y); reflexivity. Qed.

Local Arguments count_term : simpl never.

Lemma count_term_app x l l' :
  count_term x (l ++ l') = count_term x l + count_term x l'.
Proof. unfold count_term. now rewrite filter_app, length_app. Qed.

Lemma count_term_cons_neq x y l : x <> y -> count_term x (y :: l) = count_term x l.
Proof. intros H. rewrite count_term_cons. destruct (eqb_specT x y); [ congruence | reflexivity ]. Qed.

Lemma count_term_nil x : count_term x [] = 0.
Proof. reflexivity. Qed.

Lemma count_flat_map_zero {A} s (g : A -> list term) (l : list A) :
  count_term s (flat_map g l) = 0 -> forall x, In x l -> count_term s (g x) = 0.
Proof.
  induction l as [|a l IH]; cbn; [ intros _ _ [] | ].
  rewrite count_term_app. intros H x [<-|Hx]; [ lia | apply IH; [ lia | exact Hx ] ].
Qed.

Lemma count_flat_map_le {A} s (g h : A -> list term) (l : list A) :
  (forall x, count_term s (g x) <= count_term s (h x)) ->
  count_term s (flat_map g l) <= count_term s (flat_map h l).
Proof.
  intros H. induction l as [|a l IH]; cbn; [ lia | ].
  rewrite !count_term_app. specialize (H a). lia.
Qed.

Lemma count_flat_map_eq {A} s (g h : A -> list term) (l : list A) :
  (forall x, count_term s (g x) <= count_term s (h x)) ->
  count_term s (flat_map g l) = count_term s (flat_map h l) ->
  forall x, In x l -> count_term s (g x) = count_term s (h x).
Proof.
  intros Hle. induction l as [|a l IH]; cbn; [ intros _ _ [] | ].
  rewrite !count_term_app. intros Heq x Hx.
  pose proof (Hle a). pose proof (count_flat_map_le s g h l Hle).
  destruct Hx as [<-|Hx]; [ lia | apply IH; [ lia | exact Hx ] ].
Qed.

Lemma abstract_hit s k : abstract s k s = tRel k.
Proof. destruct s; cbn [abstract]; now rewrite eqb_refl. Qed.

(** No occurrence (with enough fuel): [abstract] is the identity. *)
Lemma count_collect_zero s : forall fuel t k,
  tsize t <= fuel -> count_term s (collect fuel t) = 0 -> abstract s k t = t.
Proof.
  induction fuel as [|fuel IH]; intros t k Hle H.
  { pose proof (tsize_pos t). lia. }
  cbn [collect] in H. rewrite count_term_cons in H.
  destruct (eqb s t) eqn:Est; [ lia | ]. cbn in H.
  destruct t; cbn [abstract]; rewrite Est; cbn [tsize] in Hle; try reflexivity.
  - (* tEvar *) f_equal. erewrite map_ext_in; [ apply map_id | ].
    intros x Hx. apply IH; [ pose proof (In_list_size_le tsize _ _ Hx); lia | ].
    eapply count_flat_map_zero; eassumption.
  - (* tLambda *) f_equal. apply IH; [ lia | exact H ].
  - (* tLetIn *) rewrite count_term_app in H. f_equal; apply IH; lia.
  - (* tApp *) rewrite count_term_app in H. f_equal; apply IH; lia.
  - (* tConstruct *) f_equal. erewrite map_ext_in; [ apply map_id | ].
    intros x Hx. apply IH; [ pose proof (In_list_size_le tsize _ _ Hx); lia | ].
    eapply count_flat_map_zero; eassumption.
  - (* tCase *) rewrite count_term_app in H. f_equal; [ apply IH; lia | ].
    erewrite map_ext_in; [ apply map_id | ]. intros [nas br] Hx. cbn. f_equal.
    apply IH; [ pose proof (In_list_size_le (fun b : list name × term => tsize b.2) _ _ Hx); cbn in *; lia | ].
    exact (count_flat_map_zero s (fun b : list name × term => collect fuel b.2) brs ltac:(lia) _ Hx).
  - (* tProj *) f_equal. apply IH; [ lia | exact H ].
  - (* tFix *) f_equal. erewrite map_ext_in; [ apply map_id | ]. intros [dn db ra] Hx.
    unfold map_def; cbn. f_equal.
    apply IH; [ pose proof (In_list_size_le (fun d : def term => tsize (dbody d)) _ _ Hx); cbn in *; lia | ].
    exact (count_flat_map_zero s (fun d : def term => collect fuel (dbody d)) mfix H _ Hx).
  - (* tCoFix *) f_equal. erewrite map_ext_in; [ apply map_id | ]. intros [dn db ra] Hx.
    unfold map_def; cbn. f_equal.
    apply IH; [ pose proof (In_list_size_le (fun d : def term => tsize (dbody d)) _ _ Hx); cbn in *; lia | ].
    exact (count_flat_map_zero s (fun d : def term => collect fuel (dbody d)) mfix H _ Hx).
  - (* tLazy *) f_equal. apply IH; [ lia | exact H ].
  - (* tForce *) f_equal. apply IH; [ lia | exact H ].
Qed.

Lemma count_strict_le s : forall fuel t,
  count_term s (collect_strict fuel t) <= count_term s (collect fuel t).
Proof.
  induction fuel as [|fuel IH]; intros t; [ cbn; lia | ].
  cbn [collect collect_strict]. rewrite !count_term_cons.
  destruct t; rewrite ?count_term_app, ?count_term_nil; try lia.
  - pose proof (IH t1); pose proof (IH t2); lia.
  - pose proof (IH t1); pose proof (IH t2); lia.
  - pose proof (count_flat_map_le s _ _ args IH); lia.
  - pose proof (IH t); lia.
  - pose proof (IH t); lia.
  - pose proof (IH t); lia.
Qed.

(** [strict_only s t]: every occurrence of [s] in [t] is in a strict
    position (the positions [collect_strict] descends into). *)
Inductive strict_only (s : term) : term -> Prop :=
| so_hit : strict_only s s
| so_none t : (forall k, abstract s k t = t) -> strict_only s t
| so_app f a : strict_only s f -> strict_only s a -> strict_only s (tApp f a)
| so_letin na b0 b1 :
    strict_only s b0 -> strict_only s b1 -> strict_only s (tLetIn na b0 b1)
| so_case ci d brs :
    strict_only s d ->
    (forall k nas br, In (nas, br) brs -> abstract s k br = br) ->
    strict_only s (tCase ci d brs)
| so_proj p u : strict_only s u -> strict_only s (tProj p u)
| so_construct ind c args :
    Forall (strict_only s) args -> strict_only s (tConstruct ind c args)
| so_force u : strict_only s u -> strict_only s (tForce u).

Lemma count_eq_strict_only s : forall fuel t, tsize t <= fuel ->
  count_term s (collect_strict fuel t) = count_term s (collect fuel t) ->
  strict_only s t.
Proof.
  induction fuel as [|fuel IH]; intros t Hle Heq.
  { pose proof (tsize_pos t). lia. }
  destruct (eqb_specT s t) as [<-|Hne]; [ apply so_hit | ].
  cbn [collect collect_strict] in Heq. rewrite !count_term_cons in Heq.
  destruct t as [|n|i|n l|na b|na t1 t2|t1 t2|kn|ind c args|ci t l|p t|mf idx|mf idx|p|t|t]; cbn [tsize] in Hle; rewrite ?count_term_app, ?count_term_nil in Heq;
    try solve [ apply so_none; intros k; apply (count_collect_zero s (S fuel));
      [ cbn [tsize]; lia
      | cbn [collect]; rewrite count_term_cons_neq by exact Hne;
        rewrite ?count_term_app, ?count_term_nil; lia ] ].
  - (* tLetIn *) pose proof (count_strict_le s fuel t1); pose proof (count_strict_le s fuel t2).
    apply so_letin; apply IH; lia.
  - (* tApp *) pose proof (count_strict_le s fuel t1); pose proof (count_strict_le s fuel t2).
    apply so_app; apply IH; lia.
  - (* tConstruct *) apply so_construct. apply Forall_forall. intros x Hx.
    apply IH; [ pose proof (In_list_size_le tsize _ _ Hx); lia | ].
    eapply count_flat_map_eq; [ apply count_strict_le | | exact Hx ]. lia.
  - (* tCase *) pose proof (count_strict_le s fuel t).
    apply so_case; [ apply IH; lia | ]. intros k nas br Hx.
    apply count_collect_zero with (fuel := fuel).
    + pose proof (In_list_size_le (fun b : list name × term => tsize b.2) _ _ Hx); cbn in *; lia.
    + exact (count_flat_map_zero s (fun b : list name × term => collect fuel b.2) l ltac:(lia) _ Hx).
  - (* tProj *) apply so_proj; apply IH; lia.
  - (* tForce *) apply so_force; apply IH; lia.
Qed.

(** [strict_sub s t]: [s] occurs in [t] at a strict position. *)
Inductive strict_sub (s : term) : term -> Prop :=
| ss_refl : strict_sub s s
| ss_app_l f a : strict_sub s f -> strict_sub s (tApp f a)
| ss_app_r f a : strict_sub s a -> strict_sub s (tApp f a)
| ss_letin_l na b0 b1 : strict_sub s b0 -> strict_sub s (tLetIn na b0 b1)
| ss_letin_r na b0 b1 : strict_sub s b1 -> strict_sub s (tLetIn na b0 b1)
| ss_case ci d brs : strict_sub s d -> strict_sub s (tCase ci d brs)
| ss_proj p u : strict_sub s u -> strict_sub s (tProj p u)
| ss_construct ind c args a :
    In a args -> strict_sub s a -> strict_sub s (tConstruct ind c args)
| ss_force u : strict_sub s u -> strict_sub s (tForce u).

Lemma collect_strict_sub : forall fuel t s,
  In s (collect_strict fuel t) -> strict_sub s t.
Proof.
  induction fuel as [|fuel IH]; intros t s Hin.
  - destruct Hin as [<-|[]]. apply ss_refl.
  - cbn in Hin. destruct Hin as [<-|Hin]; [ apply ss_refl | ].
    destruct t; try solve [ destruct Hin ].
    + apply in_app_or in Hin as [Hin|Hin]; [ apply ss_letin_l | apply ss_letin_r ]; eauto.
    + apply in_app_or in Hin as [Hin|Hin]; [ apply ss_app_l | apply ss_app_r ]; eauto.
    + apply in_flat_map in Hin as [x [Hx Hin]]. eapply ss_construct; eauto.
    + apply ss_case; eauto.
    + apply ss_proj; eauto.
    + apply ss_force; eauto.
Qed.

Lemma strict_sub_csubst s a k t :
  closedn 0 s -> strict_sub s t -> strict_sub s (csubst a k t).
Proof.
  intros Hs H. induction H in k |- *; cbn.
  - rewrite csubst_closed; [ apply ss_refl | eapply closed_upwards; [ exact Hs | lia ] ].
  - apply ss_app_l; auto.
  - apply ss_app_r; auto.
  - apply ss_letin_l; auto.
  - apply ss_letin_r; auto.
  - apply ss_case; auto.
  - apply ss_proj; auto.
  - eapply ss_construct; [ apply in_map; eassumption | auto ].
  - apply ss_force; auto.
Qed.

(** *** (3b) Environment lookups used by evaluation are unchanged by [cse_env]. *)

Lemma constructor_isprop_pars_decl_cse efl Σ ind c :
  constructor_isprop_pars_decl (cse_env efl Σ) ind c = constructor_isprop_pars_decl Σ ind c.
Proof. unfold constructor_isprop_pars_decl. now rewrite lookup_constructor_cse. Qed.

Lemma inductive_isprop_and_pars_cse efl Σ ind :
  inductive_isprop_and_pars (cse_env efl Σ) ind = inductive_isprop_and_pars Σ ind.
Proof. unfold inductive_isprop_and_pars. now rewrite lookup_inductive_cse. Qed.

Lemma atom_cse {wfl : WcbvFlags} efl Σ t : atom (cse_env efl Σ) t = atom Σ t.
Proof. unfold atom. destruct t; try reflexivity. now rewrite lookup_constructor_cse. Qed.

(** *** (3c) The simulation relation.

    [cse_rel t t'] holds when [t'] is [t] in which some closed subterms [s]
    at strict positions have been replaced by their value [sv] (a hole).
    Non-strict positions are left untouched, so both terms evaluate to the
    same value. *)

Section Simulation.
  Context {wfl : WcbvFlags} (efl : EEnvFlags) (Σ : global_declarations).
  Hypothesis HclΣ : closed_env Σ.
  Notation Σ' := (cse_env efl Σ).

  Inductive cse_rel : term -> term -> Prop :=
  | cr_box : cse_rel tBox tBox
  | cr_rel n : cse_rel (tRel n) (tRel n)
  | cr_var na : cse_rel (tVar na) (tVar na)
  | cr_evar n ts : cse_rel (tEvar n ts) (tEvar n ts)
  | cr_lambda na b : cse_rel (tLambda na b) (tLambda na b)
  | cr_letin na b0 b0' b1 b1' :
      cse_rel b0 b0' -> cse_rel b1 b1' -> cse_rel (tLetIn na b0 b1) (tLetIn na b0' b1')
  | cr_app f f' a a' : cse_rel f f' -> cse_rel a a' -> cse_rel (tApp f a) (tApp f' a')
  | cr_const kn : cse_rel (tConst kn) (tConst kn)
  | cr_construct ind c args args' :
      Forall2 cse_rel args args' -> cse_rel (tConstruct ind c args) (tConstruct ind c args')
  | cr_case ci d d' brs : cse_rel d d' -> cse_rel (tCase ci d brs) (tCase ci d' brs)
  | cr_proj p u u' : cse_rel u u' -> cse_rel (tProj p u) (tProj p u')
  | cr_fix mf idx : cse_rel (tFix mf idx) (tFix mf idx)
  | cr_cofix mf idx : cse_rel (tCoFix mf idx) (tCoFix mf idx)
  | cr_prim p : cse_rel (tPrim p) (tPrim p)
  | cr_lazy u : cse_rel (tLazy u) (tLazy u)
  | cr_force u u' : cse_rel u u' -> cse_rel (tForce u) (tForce u')
  | cr_hole s sv : closedn 0 s -> closedn 0 sv ->
      ∥ eval Σ s sv ∥ -> ∥ eval Σ' sv sv ∥ -> cse_rel s sv.

  Lemma cse_rel_refl t : cse_rel t t.
  Proof.
    induction t using term_forall_list_ind; try now constructor.
    apply cr_construct. induction X; constructor; auto.
  Qed.

  Lemma cse_rel_csubst a : forall k t t',
    cse_rel t t' -> cse_rel (csubst a k t) (csubst a k t').
  Proof.
    fix IH 4. intros k t t' H. destruct H.
    1-5, 8, 12-15: apply cse_rel_refl.
    - cbn. apply cr_letin; apply IH; assumption.
    - cbn. apply cr_app; apply IH; assumption.
    - cbn. apply cr_construct. revert args args' H.
      fix IHl 3. intros ? ? []; cbn; constructor; [ apply IH; assumption | apply IHl; assumption ].
    - cbn. apply cr_case; apply IH; assumption.
    - cbn. apply cr_proj; apply IH; assumption.
    - cbn. apply cr_force; apply IH; assumption.
    - rewrite (csubst_closed a k s), (csubst_closed a k sv);
        [ now apply cr_hole | eapply closed_upwards; [ eassumption | lia ]
        | eapply closed_upwards; [ eassumption | lia ] ].
  Qed.

  (** Hoisting a strict-only candidate and substituting its value back gives
      a related term. *)
  Lemma abstract_rel s sv :
    closedn 0 s -> closedn 0 sv -> ∥ eval Σ s sv ∥ -> ∥ eval Σ' sv sv ∥ ->
    forall t, strict_only s t -> forall k, closedn k t ->
    cse_rel t (csubst sv k (abstract s k t)).
  Proof.
    intros Hs Hsv Hev Hev' t.
    induction t using term_forall_list_ind; intros Hso k Hcl; inversion Hso; subst;
      try solve [ rewrite abstract_hit; cbn; rewrite Nat.compare_refl; now apply cr_hole
                | match goal with Hn : forall k, abstract _ k _ = _ |- _ => rewrite Hn end;
                  rewrite csubst_closed by exact Hcl; apply cse_rel_refl ].
    all: cbn [abstract]; match goal with |- context [eqb ?s' ?t] =>
      destruct (eqb_specT s' t) as [->|Hne] end;
      [ cbn; rewrite Nat.compare_refl; now apply cr_hole | ].
    all: cbn in Hcl |- *; rtoProp.
    - (* tLetIn *) apply cr_letin; auto.
    - (* tApp *) apply cr_app; auto.
    - (* tConstruct *) apply cr_construct.
      match goal with HF : Forall _ _ |- _ => rename HF into Hargs end.
      clear Hso Hne. induction X as [|x l Px X IHX]; cbn in *; [ constructor | ].
      inversion Hargs; subst; rtoProp. constructor; auto.
    - (* tCase *)
      match goal with |- cse_rel (tCase _ _ ?l) (tCase _ _ ?l') => replace l' with l end;
        [ apply cr_case; auto | ].
      rewrite map_map. symmetry. erewrite map_ext_in; [ apply map_id | ].
      intros [nas br] Hx. cbn.
      match goal with Hb : forall k nas br, In (nas, br) _ -> _ |- _ => rewrite (Hb _ nas br Hx) end.
      match goal with Hf : is_true (forallb _ l) |- _ =>
        pose proof (proj1 (forallb_forall _ _) Hf _ Hx) as Hc; cbn in Hc end.
      rewrite csubst_closed; [ reflexivity | eapply closed_upwards; [ exact Hc | lia ] ].
    - (* tProj *) apply cr_proj; auto.
    - (* tForce *) apply cr_force; auto.
  Qed.


  (** *** (3d) The simulation. *)

  Definition sim1 t v := forall t', cse_rel t t' -> ∥ eval Σ' t' v ∥.
  Definition sim2 t := forall s, closedn 0 s -> strict_sub s t ->
    exists sv, ∥ eval Σ s sv ∥ /\ sim1 s sv.
  Definition simP t v (ev : eval Σ t v) := sim1 t v /\ sim2 t.

  Lemma simP_intro t v (ev : eval Σ t v) :
    (forall t', cse_rel t t' ->
      ∥ eval Σ' t' v ∥ \/ (∥ eval Σ t t' ∥ /\ ∥ eval Σ' t' t' ∥)) ->
    (forall s, closedn 0 s -> strict_sub s t -> s = t \/ exists sv, ∥ eval Σ s sv ∥ /\ sim1 s sv) ->
    simP t v ev.
  Proof.
    intros H1 H2. split.
    - intros t' Hr. destruct (H1 t' Hr) as [H|[[e] [e']]]; [ exact H | ].
      now rewrite (eval_deterministic ev e).
    - intros s Hs Hss. destruct (H2 s Hs Hss) as [->|H]; [ | exact H ].
      exists v. split; [ now sq | ]. intros t' Hr.
      destruct (H1 t' Hr) as [H|[[e] [e']]]; [ exact H | ].
      now rewrite (eval_deterministic ev e).
  Qed.

  Lemma over_sim2 args args' (a : All2_Set (eval Σ) args args') :
    All2_over a (fun x y e => simP x y e) -> forall x, In x args -> sim2 x.
  Proof.
    induction a; cbn; [ intros _ _ [] | ].
    intros [h1 h2] z [<-|Hz]; [ exact (proj2 h1) | exact (IHa h2 z Hz) ].
  Qed.

  Lemma over_sim1 args args' (a : All2_Set (eval Σ) args args') :
    All2_over a (fun x y e => simP x y e) ->
    forall args0, Forall2 cse_rel args args0 -> ∥ All2_Set (eval Σ') args0 args' ∥.
  Proof.
    induction a; cbn; intros iha args0 H; inversion H; subst; [ sq; constructor | ].
    destruct iha as [[h1 _] h2]. destruct (h1 _ ltac:(eassumption)) as [e].
    destruct (IHa h2 _ ltac:(eassumption)) as [es]. sq; now constructor.
  Qed.

  Lemma Forall2_refl_rel l : Forall2 cse_rel l l.
  Proof. induction l; constructor; auto using cse_rel_refl. Qed.

  (** Evaluating [cse_term body] in the new environment. *)
  Lemma cse_term_sim body res (ev : eval Σ body res) :
    closedn 0 body -> simP body res ev -> ∥ eval Σ' (cse_term efl body) res ∥.
  Proof.
    intros Hcl [H1 H2]. unfold cse_term.
    destruct (cse_enabled efl); [ | apply H1, cse_rel_refl ].
    destruct (best_candidate _ _) as [s|] eqn:Hbest; [ | apply H1, cse_rel_refl ].
    apply best_candidate_In in Hbest. apply dedup_In in Hbest.
    apply filter_In in Hbest as [Hin Hok].
    unfold candidate_ok in Hok.
    apply andb_and in Hok as [Hok Hcnt]. apply andb_and in Hok as [Hok _].
    apply andb_and in Hok as [Hok _]. apply andb_and in Hok as [Hs _].
    apply Nat.eqb_eq in Hcnt.
    pose proof (count_eq_strict_only s (tsize body) body (le_n _) Hcnt) as Hso.
    apply collect_strict_sub in Hin.
    destruct (H2 s Hs Hin) as [sv [[evs] Hsv1]].
    destruct (Hsv1 s (cse_rel_refl s)) as [evs'].
    pose proof (eval_closed Σ HclΣ s sv Hs evs) as Hsvcl.
    pose proof (value_final _ (eval_to_value _ _ evs')) as evsv.
    destruct (H1 _ (abstract_rel s sv Hs Hsvcl (sq evs) (sq evsv) body Hso 0 Hcl)) as [e].
    sq. eapply eval_zeta; [ exact evs' | exact e ].
  Qed.


  Ltac sim1_pre := let tr := fresh "tr" in let Hrel := fresh "Hrel" in intros tr Hrel; inversion Hrel; subst;
    try solve [ right; split; assumption ].
  Ltac sim2_pre := let s := fresh "s" in let Hs := fresh "Hs" in let Hss := fresh "Hss" in intros s Hs Hss; inversion Hss; subst;
    [ left; reflexivity | .. ]; right.
  Ltac use_ih2 := match goal with
    | H : strict_sub ?s ?u, IH : simP ?u _ _, Hs : is_true (closedn 0 ?s) |- _ => exact (proj2 IH s Hs H)
    | H : strict_sub ?s ?b, IH : simP (csubst ?a 0 ?b) _ _, Hs : is_true (closedn 0 ?s) |- _ =>
        exact (proj2 IH s Hs (strict_sub_csubst s a 0 b Hs H))
    | H : strict_sub ?s ?x, Hin : In ?x _, iha : All2_over ?a _, Hs : is_true (closedn 0 ?s) |- _ =>
        exact (over_sim2 _ _ a iha x Hin s Hs H)
    end.
  Ltac ihs := repeat match goal with
    | H : cse_rel ?b ?b', IH : simP (csubst ?a 0 ?b) _ _ |- _ =>
        apply (cse_rel_csubst a 0) in H
    end;
    repeat match goal with
    | IH : simP ?x _ _, H : cse_rel ?x ?x' |- _ =>
        let e := fresh "ev" in destruct (proj1 IH _ H) as [e]; clear H
    end;
    repeat match goal with
    | IH : simP ?x _ _ |- _ =>
        let e := fresh "ev" in destruct (proj1 IH _ (cse_rel_refl x)) as [e]; clear IH
    end.

  Ltac evtac := rewrite ?constructor_isprop_pars_decl_cse, ?inductive_isprop_and_pars_cse,
    ?lookup_constructor_cse, ?atom_cse; eauto.
  Ltac fin := ihs; sq; first
    [ solve [ eapply eval_box; evtac ] | solve [ eapply eval_beta; evtac ]
    | solve [ eapply eval_zeta; evtac ] | solve [ eapply eval_iota; evtac ]
    | solve [ eapply eval_iota_block; evtac ] | solve [ eapply eval_iota_sing; evtac ]
    | solve [ eapply eval_fix; evtac ] | solve [ eapply eval_fix_value; evtac ]
    | solve [ eapply eval_fix'; evtac ] | solve [ eapply eval_cofix_case; evtac ]
    | solve [ eapply eval_cofix_proj; evtac ] | solve [ eapply eval_proj; evtac ]
    | solve [ eapply eval_proj_block; evtac ] | solve [ eapply eval_proj_prop; evtac ]
    | solve [ eapply eval_construct; evtac ] | solve [ eapply eval_app_cong; evtac ]
    | solve [ eapply eval_force; evtac ] | solve [ eapply eval_atom; evtac ] ].

  Lemma cse_sim t v (ev : eval Σ t v) : simP t v ev.
  Proof.
    induction ev using eval_rect; (apply simP_intro; [ sim1_pre | sim2_pre ]).
    all: try solve [ use_ih2 ].
    all: try solve [ left; fin ].
    (* atom: structurally related forms are not atoms *)
    all: try solve [ exfalso; match goal with H : is_true (atom _ _) |- _ => cbn in H; congruence end ].
    all: try solve [ match goal with H : is_true (atom _ (tConstruct _ _ ?l)) |- _ =>
        destruct l; [ | cbn in H; congruence ] end;
      first [ exfalso; match goal with Hin : In _ [] |- _ => destruct Hin end
            | left; match goal with HF : Forall2 _ [] _ |- _ => inversion HF; subst end;
              sq; apply eval_atom; now rewrite atom_cse ] ].
    - (* delta *)
      left. match goal with isdecl : declared_constant Σ ?c ?decl, e : cst_body ?decl = Some ?body,
          IH : simP ?body ?res ?ev |- _ =>
        pose proof (lookup_env_closed HclΣ isdecl) as Hcl; cbn in Hcl; rewrite e in Hcl; cbn in Hcl;
        destruct (cse_term_sim body res ev Hcl IH) as [e'];
        sq; eapply eval_delta with (decl := cse_in_constant_body efl decl);
        [ unfold declared_constant; rewrite lookup_env_cse, isdecl; reflexivity
        | cbn; rewrite e; reflexivity | exact e' ] end.
    - (* construct block *)
      left. match goal with H : Forall2 cse_rel _ ?l, iha : All2_over ?a _ |- _ =>
        destruct (over_sim1 _ _ a iha _ H) as [es]; pose proof (Forall2_length H) end.
      sq; eapply eval_construct_block; tea; [ rewrite lookup_constructor_cse; eassumption | lia ].
    - (* prim *)
      left. depelim X; try solve [ sq; eapply eval_prim; constructor ].
      match goal with ev : All2_Set _ ?v _, a : All2_over ?ev _ |- _ =>
        destruct (over_sim1 _ _ ev a _ (Forall2_refl_rel v)) as [evs] end.
      match goal with IH : simP ?d _ _ |- _ => destruct (proj1 IH _ (cse_rel_refl d)) as [evd] end.
      sq; eapply eval_prim; now constructor.
  Qed.

End Simulation.

Theorem cse_pres_eval (efl : EEnvFlags) (wfl : WcbvFlags) (Σ : global_declarations)
    (t v : term) :
  wf_glob Σ ->
  wellformed Σ 0 t ->
  EWcbvEval.eval (wfl := wfl) Σ t v ->
  ∥ EWcbvEval.eval (wfl := wfl) (cse_env efl Σ) (cse_term efl t) v ∥.
Proof.
  intros Hwf Hwt ev.
  pose proof (wellformed_closed_env (efl := efl) Hwf) as HclΣ.
  exact (cse_term_sim efl Σ HclΣ t v ev (wellformed_closed Hwt) (cse_sim efl Σ HclΣ t v ev)).
Qed.

Lemma cse_pres (efl : EEnvFlags) (wfl : WcbvFlags) (p : eprogram) (v : term) :
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (cse_program efl p) v' /\ v' = v.
Proof.
  intros [Hglob Hmain] [Hev]. exists v. split; [ | reflexivity ].
  exact (cse_pres_eval efl wfl p.1 p.2 v Hglob Hmain Hev).
Qed.

Import Transform.

Program Definition cse_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "common subexpression elimination";
     transform p _ := cse_program efl p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  now apply cse_wf.
Qed.
Next Obligation.
  now eapply cse_pres.
Qed.

Import EProgram EGlobalEnv.

(** ** (4) The transform preserves environment extension, discharging both
       [TransformExt] obligations. *)
Lemma extends_cse efl Σ Σ' :
  extends Σ Σ' -> extends (cse_env efl Σ) (cse_env efl Σ').
Proof.
  intros H kn decl. rewrite !lookup_env_cse.
  destruct (lookup_env Σ kn) as [d0|] eqn:E; cbn; [ | discriminate ].
  intros [= <-]. now rewrite (H kn d0 E).
Qed.

#[global]
Lemma cse_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (cse_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros efl wfl p p' pr pr' Hext. cbn. now apply extends_cse.
Qed.

#[global]
Lemma cse_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (cse_transformation efl wfl)
    extends_eprogram extends_eprogram.
Proof.
  intros efl wfl p p' pr pr' [Hext Heq]. split; cbn.
  - now apply extends_cse.
  - now rewrite Heq.
Qed.
