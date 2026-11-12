(** * Instance / dictionary specialization for untyped lambda-box

    This module implements the instance-specialization pass on untyped
    lambda-box terms ([EAst]).  Correctness and wellformedness preservation
    are axioms (see "Verification status" below).

    Motivation.  Typeclass-heavy frontends (notably Lean) erase to lambda-box
    in which even trivial arithmetic drags in dictionary values: [1 + 1] is
    elaborated to [HAdd.add instHAdd 1 1] where [instHAdd] is a *statically
    known* record/constructor value.  Lean's own compiler removes this cost
    with instance / typeclass-instance specialization.  This module is the
    Peregrine middle-end analogue, so every frontend benefits.

    What this pass does.  It is a *local, terminating partial evaluator* over
    lambda-box terms performing the two reductions that expose and then discard
    dictionary plumbing but that plain beta reduction ([EBeta]) does not on its
    own complete:

      - beta:  [(fun x => b) a]                          ==>  b[x := a]
      - iota:  [match C a0 .. an with | .. | C xs => br | .. end]
                                                          ==>  br[xs := a..]
               i.e. case-of-known-constructor.  In post-[verified_lambdabox]
               lambda-box, record projections have been compiled to [tCase]
               with constructors-as-blocks, so a dictionary field access is a
               [tCase] on a literal [tConstruct]; firing iota here is exactly
               the "read a field out of a known dictionary" step.

    Cloning driver (implemented below, [drive_env]).
    On top of the local reducer, the pass *clones* a function at call sites
    where a leading argument is a statically-known dictionary value: for [f d x]
    with [d] a closed dictionary [tConstruct] (or a [tConst] whose body unfolds
    to one), it emits a specialized copy [f$specN] whose body is [f]'s body with
    [d] substituted in (via [spec_beta]; for a [tConst] whose body is a [tFix],
    the fixpoint is unfolded once first), so the beta/iota reductions above fire
    *inside* [f]'s body across the call boundary; the call site is redirected to
    [f$specN x].  A dictionary argument is
    recognised by the heuristic "closed constructor whose inductive is a
    single-constructor record" ([dict_value]/[is_record_ind]), which excludes
    ordinary data (nat, list, bool, ...).  Specializations are memoised in a map
    keyed by [(callee, dicts)] so each is emitted once, and the whole search is
    bounded by a fuel budget ([specialize_fuel]) to guarantee termination and
    avoid code blow-up.  The saturation loop re-scans each freshly emitted body
    so chained dictionary plumbing (a method that itself projects another
    dictionary) is specialized too.  The local reducer below is the cleanup that
    the cloning relies on, and is independently useful after user-directed
    constant inlining ([inlinings_opts] / [EInlining]) brings an instance
    definition to a call site.

    Composition with existing passes.
      - It runs in [Transforms.extra_unsafe_transforms], that is after
        [betared] and dead-argument elimination, which run earlier in
        [optional_unsafe_transforms].  Neither cleans up after it: redexes this
        single bottom-up pass leaves behind stay, and so does a parameter that
        specialization makes unused.  It runs only in the untyped pipeline.
      - It does NOT subsume any of them: dearg removes *dead* args (it cannot
        touch a dictionary that is still projected), betared does beta but not
        iota-on-constructor, and [EInlining] inlines *named constants* uniformly
        rather than specializing a shared function per call site.

    Verification status.  Wellformedness preservation is proved
    ([specialize_instances_program_wf], for any environment flags with
    [has_tApp]): generated names are checked against the input environment
    and the earlier generated names ([fresh_name]), specializations are
    emitted depth first so that each one refers only to declarations below it
    ([spec_key]), and the iota step fires only when the constructor has as
    many arguments as the branch binds.  Evaluation preservation is not
    claimed: the transformation relates values by the trivial observational
    equivalence and assumes only termination of the target
    ([trust_specialize_instances_terminates], stated at the flags of the
    pipeline stage, [EExtraFlags]). *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils ReflectEq.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EReflect ELiftSubst EGlobalEnv EProgram.

Import ListNotations.

(** Generic congruence recursor (identical in spirit to [EBeta.map_subterms]);
    kept local so the head-reduction fixpoint below is guarded. *)
Definition spec_map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs => tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | tPrim p => tPrim (map_prim f p)
  | tLazy t => tLazy (f t)
  | tForce t => tForce (f t)
  | tConstruct ind n args => tConstruct ind n (map f args)
  | tRel n => tRel n
  | tVar na => tVar na
  | tConst kn => tConst kn
  | tBox => tBox
  end.

Section specialize.

  (** Apply an already-reduced [body] to a spine of already-reduced [args],
      firing beta as far as [body] is a literal lambda. *)
  Fixpoint spec_beta (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
        match body with
        | tLambda na body => spec_beta (body {0 := a}) args
        | _ => mkApps body (a :: args)
        end
    end.

  (** Bottom-up single pass: reduce children first, then attempt one head
      beta (via the collected spine) or iota (case-of-known-constructor). *)
  Fixpoint spec_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd arg => spec_aux (spec_aux [] arg :: args) hd
    | tLambda na body =>
        let b := spec_aux [] body in
        spec_beta (tLambda na b) args
    | tCase (ind, npar) disc brs =>
        let disc' := spec_aux [] disc in
        let brs' := map (on_snd (spec_aux [])) brs in
        let reduced :=
          match disc' with
          | tConstruct _ c cargs =>
              match nth_error brs' c with
              (* Not [iota_red]: its [substl] assumes closed arguments, and here
                 they may refer to binders around the [tCase]. *)
              | Some br =>
                  (* Only when the constructor has as many arguments as the
                     branch binds: otherwise the substitution would capture
                     or free variables (the case is stuck anyway). *)
                  if Nat.eqb #|skipn npar cargs| #|fst br|
                  then subst (List.rev (skipn npar cargs)) 0 (snd br)
                  else tCase (ind, npar) disc' brs'
              | None => tCase (ind, npar) disc' brs'
              end
          | _ => tCase (ind, npar) disc' brs'
          end in
        mkApps reduced args
    | t => mkApps (spec_map_subterms (spec_aux []) t) args
    end.

  Definition specialize_instances : term -> term := spec_aux [].

End specialize.

(** Iota with open constructor arguments keeps them apart. *)
Example specialize_instances_open_iota (i : inductive) :
  specialize_instances
    (tLambda nAnon (tLambda nAnon
       (tCase (i, 0) (tConstruct i 0 [tRel 1; tRel 0])
          [([nAnon; nAnon], tApp (tRel 1) (tRel 0))])))
  = tLambda nAnon (tLambda nAnon (tApp (tRel 1) (tRel 0))).
Proof. reflexivity. Qed.

(** ** Cloning driver

    Detect [tConst nm] applied to a leading run of closed dictionary
    constructors, emit a specialized copy of [nm] with those dictionaries
    substituted into its body, and redirect the call site to the copy. *)

Definition dkey : Type := kername × list term.

(** Boolean equality on specialization keys, built from the [ReflectEq]
    instances for [kername] and [term]; used for memoisation. *)
Fixpoint list_eqb {A} (f : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1, b :: l2 => f a b && list_eqb f l1 l2
  | _, _ => false
  end.

Definition eqb_key (k1 k2 : dkey) : bool :=
  eqb (fst k1) (fst k2) && list_eqb (fun a b => eqb a b) (snd k1) (snd k2).

(** Candidate name for the [i]-th specialization of [nm]. *)
Definition spec_name (nm : kername) (i : nat) : kername :=
  (nm.1, (nm.2 ++ "$spec" ++ string_of_nat i)%bs).

(** A name for a specialization of [nm] that is declared neither in [Σ] nor
    for an earlier specialization (the names in [seen]): the first free
    candidate from index [i] on.  [None] only when [fuel] runs out, which
    cannot happen for [fuel > #|Σ| + #|seen|]. *)
Fixpoint fresh_from (Σ : global_declarations) (seen : list (dkey × kername))
  (nm : kername) (fuel i : nat) {struct fuel} : option kername :=
  match fuel with
  | 0 => None
  | S fuel' =>
      let c := spec_name nm i in
      match lookup_env Σ c with
      | None =>
          if existsb (fun p => eqb (snd p) c) seen
          then fresh_from Σ seen nm fuel' (S i)
          else Some c
      | Some _ => fresh_from Σ seen nm fuel' (S i)
      end
  end.

Definition fresh_name (Σ : global_declarations) (seen : list (dkey × kername))
  (nm : kername) : option kername :=
  fresh_from Σ seen nm (S (#|Σ| + #|seen|)) #|seen|.

(** Is [ind] a single-constructor record (the typeclass/dictionary shape)? *)
Definition is_record_ind (Σ : global_declarations) (ind : inductive) : bool :=
  match lookup_inductive Σ ind with
  | Some (_, oib) => Nat.eqb #|oib.(ind_ctors)| 1
  | None => false
  end.

(** If [t] is a statically-known dictionary value, return the underlying
    (closed, single-constructor) [tConstruct].  Resolves one level of [tConst]
    delta so that a dictionary supplied as a named instance still qualifies. *)
Definition dict_value (Σ : global_declarations) (t : term) : option term :=
  match t with
  | tConstruct ind _ _ =>
      if is_record_ind Σ ind && closedn 0 t then Some t else None
  | tConst c =>
      match lookup_constant Σ c with
      | Some cb =>
          match cst_body cb with
          | Some (tConstruct ind n args) =>
              if is_record_ind Σ ind && closedn 0 (tConstruct ind n args)
              then Some (tConstruct ind n args) else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

(** A spine element that belongs in a specialization prefix: either an erased
    type argument ([tBox], which typically precedes the dictionaries after
    erasure) or a statically-known dictionary value.  The boolean flags whether
    it is an actual dictionary (so only prefixes that contain at least one
    dictionary are specialized). *)
Definition prefix_elt (Σ : global_declarations) (t : term) : option (bool * term) :=
  match dict_value Σ t with
  | Some d => Some (true, d)
  | None => match t with tBox => Some (false, tBox) | _ => None end
  end.

(** Split a spine into its leading prefix of erased-type/dictionary arguments
    (resolved to the values to substitute) and the remaining ordinary
    arguments; the boolean reports whether the prefix contains a dictionary. *)
Fixpoint split_dicts (Σ : global_declarations) (spine : list term)
  : bool * list term * list term :=
  match spine with
  | [] => (false, [], [])
  | a :: rest =>
      match prefix_elt Σ a with
      | Some (isd, v) =>
          let '(d', ds, rr) := split_dicts Σ rest in (orb isd d', v :: ds, rr)
      | None => (false, [], spine)
      end
  end.

Definition callee_body (Σ : global_declarations) (nm : kername) : option term :=
  match lookup_constant Σ nm with
  | Some cb => cst_body cb
  | None => None
  end.

(** Body of a specialized copy: substitute the dictionaries into the callee
    body (for a [tFix]-bodied constant, unfold the fixpoint once first), then
    run the local beta/iota reducer to collapse the exposed projections. *)
Definition spec_body (b : term) (dicts : list term) : term :=
  match b with
  | tFix mfix idx =>
      match cunfold_fix mfix idx with
      | Some (_, fn) => specialize_instances (spec_beta fn dicts)
      | None => specialize_instances (mkApps b dicts)
      end
  | _ => specialize_instances (spec_beta b dicts)
  end.

(** Key of a specializable [tConst nm] call [nm @ spine], with the ordinary
    (non-dictionary) remainder of the spine. *)
Definition mk_key (Σ : global_declarations) (nm : kername) (spine : list term)
  : option (dkey * list term) :=
  match callee_body Σ nm with
  | Some _ =>
      let '(saw_dict, dicts, rest) := split_dicts Σ spine in
      if saw_dict then Some ((nm, dicts), rest) else None
  | None => None
  end.

(** Collect every specialization key reachable in a term (spine accumulator in
    the head position, exactly as [spec_aux]). *)
Fixpoint collect_keys (Σ : global_declarations) (spine : list term) (t : term)
  {struct t} : list dkey :=
  match t with
  | tApp hd arg => collect_keys Σ [] arg ++ collect_keys Σ (arg :: spine) hd
  | tConst nm => match mk_key Σ nm spine with Some (k, _) => [k] | None => [] end
  | tLambda _ b => collect_keys Σ [] b
  | tLetIn _ v b => collect_keys Σ [] v ++ collect_keys Σ [] b
  | tCase _ disc brs =>
      collect_keys Σ [] disc ++ concat (map (fun br => collect_keys Σ [] (snd br)) brs)
  | tProj _ c => collect_keys Σ [] c
  | tFix mfix _ => concat (map (fun d => collect_keys Σ [] (dbody d)) mfix)
  | tCoFix mfix _ => concat (map (fun d => collect_keys Σ [] (dbody d)) mfix)
  | tConstruct _ _ args => concat (map (fun a => collect_keys Σ [] a) args)
  | tEvar _ args => concat (map (fun a => collect_keys Σ [] a) args)
  | tLazy t => collect_keys Σ [] t
  | tForce t => collect_keys Σ [] t
  | _ => []
  end.

Definition lookup_spec (seen : list (dkey × kername)) (k : dkey) : option kername :=
  match find (fun p => eqb_key (fst p) k) seen with
  | Some p => Some (snd p)
  | None => None
  end.

(** Redirect specializable call sites to their emitted copies (pure rewrite;
    the memo table [seen] is fixed). *)
Fixpoint redirect (Σ : global_declarations) (seen : list (dkey × kername))
  (spine : list term) (t : term) {struct t} : term :=
  match t with
  | tApp hd arg => redirect Σ seen (redirect Σ seen [] arg :: spine) hd
  | tConst nm =>
      match mk_key Σ nm spine with
      | Some (k, rest) =>
          match lookup_spec seen k with
          | Some fn => mkApps (tConst fn) rest
          | None => mkApps (tConst nm) spine
          end
      | None => mkApps (tConst nm) spine
      end
  | _ => mkApps (spec_map_subterms (redirect Σ seen []) t) spine
  end.

Definition specialize_fuel : nat := 1000.

(** State of the driver: the memo table, the output environment built so far
    (newest first), and the number of specializations that may still be
    generated in the current batch. *)
Definition spec_state : Type :=
  (list (dkey × kername) × global_declarations) × nat.

(** Generate the specialization for key [k], after the specializations its
    own body needs (depth first), and put it on top of the output
    environment.  Its body is redirected with the memo table as it is at that
    point, so it refers only to declarations that are already below it: the
    output is well-ordered by construction.  The state is returned unchanged
    when [k] is already specialized, is being specialized further up
    ([stack], a cyclic key), has no body, or when the budget, the depth
    [fuel] or the name search is exhausted; the call sites of [k] then keep
    calling the original constant. *)
Fixpoint spec_key (Σ : global_declarations) (fuel : nat) (stack : list dkey)
  (st : spec_state) (k : dkey) {struct fuel} : spec_state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      let '(seen, env, budget) := st in
      match budget with
      | 0 => st
      | S budget' =>
          if existsb (fun p => eqb_key (fst p) k) seen || existsb (eqb_key k) stack
          then st
          else
            match callee_body Σ (fst k) with
            | None => st
            | Some b =>
                let body := spec_body b (snd k) in
                let '(seen', env', budget'') :=
                  fold_left (spec_key Σ fuel' (k :: stack))
                    (collect_keys Σ [] body) (seen, env, budget') in
                match fresh_name Σ seen' (fst k) with
                | None => (seen', env', budget'')
                | Some fn =>
                    let body' := specialize_instances (redirect Σ seen' [] body) in
                    ((k, fn) :: seen',
                     (fn, ConstantDecl {| cst_body := Some body' |}) :: env',
                     budget'')
                end
            end
      end
  end.

(** Generate the specializations [keys] need, with a fresh budget. *)
Definition spec_keys (Σ : global_declarations) (keys : list dkey)
  (seen : list (dkey × kername)) (env : global_declarations)
  : list (dkey × kername) × global_declarations :=
  (fold_left (spec_key Σ specialize_fuel []) keys (seen, env, specialize_fuel)).1.

Definition body_keys (Σ : global_declarations) (d : global_decl) : list dkey :=
  match d with
  | ConstantDecl cb => match cst_body cb with
                       | Some b => collect_keys Σ [] b
                       | None => [] end
  | _ => []
  end.

Definition red_decl (Σ : global_declarations) (seen : list (dkey × kername))
  (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cb =>
      ConstantDecl {| cst_body :=
        option_map (fun b => specialize_instances (redirect Σ seen [] b))
                   (cst_body cb) |}
  | _ => d
  end.

(** One declaration [kd] of the input, given the output for the older ones:
    the specializations its body needs go right below it. *)
Definition drive_decl (Σ : global_declarations) (kd : kername × global_decl)
  (acc : list (dkey × kername) × global_declarations)
  : list (dkey × kername) × global_declarations :=
  let '(seen', env') := spec_keys Σ (body_keys Σ (snd kd)) acc.1 acc.2 in
  (seen', (fst kd, red_decl Σ seen' (snd kd)) :: env').

(** Whole-program driver.  The environment is newest-first and a declaration
    may refer only to older ones, so the declarations are processed oldest
    first: before each declaration [d], the specializations its body needs
    (and those their bodies need) are generated and placed right below [d].
    Everything such a specialization refers to (the callee, its body, the
    dictionaries and their fields) is older than [d], so the result is again a
    well-ordered environment ([drive_env_wf] below).  The specializations the
    main term needs go on top.  Bodies and the main term are redirected and
    locally reduced. *)
Definition drive_env (Σ : global_declarations) (main : term)
  : global_declarations × term :=
  let acc := fold_right (drive_decl Σ) ([], []) Σ in
  let '(seen', env') := spec_keys Σ (collect_keys Σ [] main) acc.1 acc.2 in
  (env', specialize_instances (redirect Σ seen' [] main)).

Definition specialize_instances_program (p : program) : program :=
  drive_env p.1 p.2.

(** ** Well-formedness preservation *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Erasure Require Import EWellformed EWcbvEval EInduction EExtends.
From MetaRocq.Common Require Import Transform.
From Equations Require Import Equations.

Lemma fold_left_inv {A B} (P : A -> Prop) (Q : B -> Prop) (f : A -> B -> A) l :
  (forall a b, P a -> Q b -> P (f a b)) ->
  Forall Q l -> forall a, P a -> P (fold_left f l a).
Proof.
  intros hf. induction 1; cbn; auto.
Qed.

Section WfTerm.
  Context {efl : EEnvFlags} {hasapp : has_tApp}.

  (** *** Terms *)

  Ltac wf_congr :=
    simpl in *; rewrite -> ?andb_and in *; autorewrite with map;
    simpl wellformed in *; intuition auto;
    unfold wf_fix, test_def, test_snd in *;
    try solve [repeat (rtoProp; simpl in *; solve_all)]; try easy.

  Lemma wf_closed_down Σ t :
    forall k k', wellformed Σ k t -> closedn k' t -> wellformed Σ k' t.
  Proof.
    induction t using term_forall_list_ind; intros; wf_congr.
    - destruct cstr_as_blocks; auto. rtoProp; intuition auto. solve_all.
    - depelim X; simpl in *; rtoProp; intuition eauto; solve_all.
      depelim H; constructor; cbn in *; intuition eauto; solve_all.
  Qed.

  Lemma wf_spec_beta Σ args :
    forall body k, wellformed Σ k body -> forallb (wellformed Σ k) args ->
    wellformed Σ k (spec_beta body args).
  Proof.
    induction args as [|a args IH]; intros body k hb ha; cbn; auto.
    move/andP: ha => [ha has].
    assert (hd : wellformed Σ k (mkApps body (a :: args))).
    { rewrite wellformed_mkApps //. apply/andP; split => //. now apply/andP; split. }
    destruct body; try exact hd.
    apply IH; auto. cbn in hb. move/andP: hb => [_ hb].
    apply (wellformed_subst [a]); cbn; [now rewrite ha|exact hb].
  Qed.

  Lemma wf_construct_args Σ k i c args :
    wellformed Σ k (tConstruct i c args) -> forallb (wellformed Σ k) args.
  Proof.
    simpl. move/andP => [_]. destruct cstr_as_blocks.
    - now move/andP => [_].
    - now destruct args.
  Qed.

  Lemma wf_spec_aux Σ t :
    forall k args, wellformed Σ k t -> forallb (wellformed Σ k) args ->
    wellformed Σ k (spec_aux args t).
  Proof.
    induction t using term_forall_list_ind; intros k sp hw ha.
    all: try solve [cbn [spec_aux spec_map_subterms]; rewrite wellformed_mkApps //;
                    apply/andP; split; [|exact ha]; clear ha; wf_congr].
    - (* tLambda *)
      cbn [spec_aux]. apply wf_spec_beta; auto.
      simpl in hw |- *. move/andP: hw => [hl hw]. rewrite hl /=. now apply IHt.
    - (* tApp *)
      cbn [spec_aux]. simpl in hw. move/andP: hw => [/andP [happ h1] h2].
      apply IHt1 => //. cbn [forallb]. rewrite ha andb_true_r. now apply IHt2.
    - (* tConstruct *)
      cbn [spec_aux spec_map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [-> hw] /=.
      destruct cstr_as_blocks.
      + move/andP: hw => [h1 h2]. rewrite length_map h1 /=. solve_all.
      + destruct args => //.
    - (* tCase *)
      destruct p as [ind npar]. cbn [spec_aux].
      simpl in hw. move/andP: hw => [hcase /andP [/andP [hcs hd] hbrs]].
      assert (hd' : wellformed Σ k (spec_aux [] t)) by now apply IHt.
      assert (hbrs' : forallb (fun br => wellformed Σ (#|br.1| + k) br.2)
                        (map (on_snd (spec_aux [])) l)).
      { clear -X hbrs. solve_all. }
      assert (hc : wellformed Σ k (tCase (ind, npar) (spec_aux [] t)
                                    (map (on_snd (spec_aux [])) l))).
      { simpl. rewrite length_map hcase hcs hd' /=. exact hbrs'. }
      rewrite wellformed_mkApps //. apply/andP; split; [|exact ha].
      destruct (spec_aux [] t) eqn:hdisc; try exact hc.
      destruct (nth_error _ n) as [br|] eqn:hnth; try exact hc.
      destruct (Nat.eqb_spec #|skipn npar args| #|br.1|) as [hlen|]; try exact hc.
      apply wellformed_subst.
      + rewrite forallb_rev. apply wf_construct_args in hd'.
        now apply forallb_skipn.
      + rewrite List.length_rev hlen.
        eapply nth_error_forallb in hbrs'; tea. exact hbrs'.
    - (* tFix *)
      cbn [spec_aux spec_map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [hl hw].
      apply/andP; split.
      + clear hw X. move/andP: hl => [-> hl] /=. solve_all. destruct x as [? [] ?] => //.
      + unfold wf_fix_gen in *. rewrite length_map.
        move/andP: hw => [-> hw] /=. unfold test_def in *. solve_all.
  Qed.

  Lemma split_dicts_rest Σ0 (P : term -> bool) spine :
    forallb P spine -> forallb P (split_dicts Σ0 spine).2.
  Proof.
    induction spine as [|a spine IH]; cbn [split_dicts]; auto.
    intros h. destruct (prefix_elt Σ0 a) as [[isd v]|]; auto.
    move/andP: h => [_ h]. specialize (IH h).
    now destruct (split_dicts Σ0 spine) as [[d' ds] rr].
  Qed.

  Lemma mk_key_rest Σ0 (P : term -> bool) nm spine key rest :
    mk_key Σ0 nm spine = Some (key, rest) -> forallb P spine -> forallb P rest.
  Proof.
    unfold mk_key. destruct callee_body => //. intros h hs.
    apply (split_dicts_rest Σ0) in hs.
    destruct (split_dicts Σ0 spine) as [[d' ds] rr]. destruct d' => //.
    now noconf h.
  Qed.

  Lemma wf_redirect Σ0 seen Σ t :
    (forall key fn, lookup_spec seen key = Some fn ->
       exists cb, lookup_constant Σ fn = Some cb /\ isSome (cst_body cb)) ->
    forall k sp, wellformed Σ k t -> forallb (wellformed Σ k) sp ->
    wellformed Σ k (redirect Σ0 seen sp t).
  Proof.
    intros hseen.
    induction t using term_forall_list_ind; intros k sp hw ha.
    all: try solve [cbn [redirect spec_map_subterms]; rewrite wellformed_mkApps //;
                    apply/andP; split; [|exact ha]; clear ha; wf_congr].
    - (* tApp *)
      cbn [redirect]. simpl in hw. move/andP: hw => [/andP [happ h1] h2].
      apply IHt1 => //. cbn [forallb]. rewrite ha andb_true_r. now apply IHt2.
    - (* tConst *)
      cbn [redirect].
      destruct mk_key as [[key rest]|] eqn:hk;
        [destruct lookup_spec as [fn|] eqn:hls|].
      all: rewrite wellformed_mkApps //; apply/andP; split; auto.
      + simpl in hw |- *. move/andP: hw => [-> _] /=.
        destruct (hseen _ _ hls) as [cb [-> hb]]. now rewrite hb orb_true_r.
      + eapply mk_key_rest; tea.
    - (* tConstruct *)
      cbn [redirect spec_map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [-> hw] /=.
      destruct cstr_as_blocks.
      + move/andP: hw => [h1 h2]. rewrite length_map h1 /=. solve_all.
      + destruct args => //.
    - (* tFix *)
      cbn [redirect spec_map_subterms]. rewrite wellformed_mkApps //.
      apply/andP; split; [|exact ha]. clear ha.
      simpl in hw |- *. move/andP: hw => [hl hw].
      apply/andP; split.
      + clear hw X. move/andP: hl => [-> hl] /=. solve_all. destruct x as [? [] ?] => //.
      + unfold wf_fix_gen in *. rewrite length_map.
        move/andP: hw => [-> hw] /=. unfold test_def in *. solve_all.
  Qed.

  Lemma wf_spec_body Σ b dicts :
    wellformed Σ 0 b -> forallb (wellformed Σ 0) dicts ->
    wellformed Σ 0 (spec_body b dicts).
  Proof.
    intros hb hd. unfold spec_body, specialize_instances.
    destruct b; try (apply wf_spec_aux => //; now apply wf_spec_beta).
    destruct cunfold_fix as [[n f]|] eqn:hc; apply wf_spec_aux => //.
    - apply wf_spec_beta => //. eapply wellformed_cunfold_fix; tea.
    - now rewrite wellformed_mkApps // hb hd.
  Qed.

End WfTerm.

(** *** Environments that agree up to constant bodies *)

Definition decl_sim (d d' : global_decl) : Prop :=
  match d, d' with
  | ConstantDecl cb, ConstantDecl cb' => isSome (cst_body cb) -> isSome (cst_body cb')
  | InductiveDecl m, InductiveDecl m' => m = m'
  | _, _ => False
  end.

Definition env_sim (Σ Σ' : global_declarations) : Prop :=
  forall kn d, lookup_env Σ kn = Some d ->
  exists d', lookup_env Σ' kn = Some d' /\ decl_sim d d'.

Section Sim.
  Context {efl : EEnvFlags}.

  Lemma sim_wellformed Σ Σ' :
    env_sim Σ Σ' -> forall t n, wellformed Σ n t -> wellformed Σ' n t.
  Proof.
    intros hs t.
    induction t using term_forall_list_ind; cbn => //; intros; rtoProp; intuition auto; solve_all.
    all: try (destruct (lookup_env Σ _) as [g|] eqn:hl => //;
              destruct (hs _ _ hl) as [d' [hl' hd]]; rewrite hl';
              destruct g, d' => //; cbn in hd; subst).
    all: try assumption.
    - move/orP: H0 => [->|h] //. now rewrite (hd h) orb_true_r.
    - destruct cstr_as_blocks; eauto; rtoProp; intuition auto; solve_all.
    - move: H0. rewrite /wf_brs /lookup_inductive /lookup_minductive /=.
      destruct (lookup_env Σ _) as [g|] eqn:hl => //.
      destruct (hs _ _ hl) as [d' [-> hd]].
      destruct g, d' => //; cbn in hd; subst => //.
    - move/andP: H0 => [] hn hf. unfold wf_fix. rewrite hn /=. solve_all.
    - move/andP: H0 => [] hn hf. unfold wf_fix. rewrite hn /=. solve_all.
  Qed.

End Sim.

(** *** The driver preserves well-formedness *)

Section Driver.
  Context {efl : EEnvFlags} {hasapp : has_tApp}.
  Context (Σ : global_declarations).

  Lemma fresh_from_spec seen nm fuel i c :
    fresh_from Σ seen nm fuel i = Some c ->
    lookup_env Σ c = None /\ ~ In c (map snd seen).
  Proof.
    induction fuel in i |- *; simpl => //.
    destruct (lookup_env Σ (spec_name nm i)) eqn:hl; [apply IHfuel|].
    destruct (existsb _ seen) eqn:hex; [apply IHfuel|].
    intros [= <-]. split => //.
    intros hin. apply in_map_iff in hin as [p [hp hin]].
    enough (existsb (fun p => snd p == spec_name nm i) seen = true) by congruence.
    apply existsb_exists. exists p; split => //. rewrite hp. apply eqb_refl.
  Qed.

  Lemma lookup_spec_In seen k fn :
    lookup_spec seen k = Some fn -> In fn (map snd seen).
  Proof.
    unfold lookup_spec. destruct find eqn:hf => //. intros [= <-].
    apply find_some in hf as [hin _]. now apply in_map.
  Qed.

  Lemma lookup_None_fresh (E : global_declarations) kn :
    lookup_env E kn = None -> fresh_global kn E.
  Proof.
    induction E as [|[kn' d] E IH]; cbn; [constructor|].
    destruct (eqb_spec kn kn') => // h. constructor; [cbn; congruence|now apply IH].
  Qed.

  (** Invariant relating the part [Σs] of the input processed so far (a
      suffix of [Σ]), the memo table and the output environment. *)
  Record spec_inv (Σs : global_declarations) (seen : list (dkey × kername))
    (env : global_declarations) : Prop :=
    { inv_wf : wf_glob env;
      inv_sim : env_sim Σs env;
      inv_seen : forall fn, In fn (map snd seen) ->
          lookup_env Σ fn = None /\
          exists cb, lookup_constant env fn = Some cb /\ isSome (cst_body cb);
      inv_names : forall kn d, lookup_env env kn = Some d ->
          isSome (lookup_env Σs kn) \/ In kn (map snd seen) }.

  Lemma wf_final Σs seen env t :
    spec_inv Σs seen env -> wellformed Σs 0 t ->
    wellformed env 0 (specialize_instances (redirect Σ seen [] t)).
  Proof.
    intros hi hw. apply (wf_spec_aux (hasapp := hasapp)) => //. apply (wf_redirect (hasapp := hasapp)) => //.
    - intros key fn hl. apply lookup_spec_In in hl. now apply (inv_seen _ _ _ hi).
    - eapply sim_wellformed; tea. apply hi.
  Qed.

  Lemma spec_inv_add Σs seen env k fn body :
    extends Σs Σ ->
    spec_inv Σs seen env ->
    lookup_env Σ fn = None -> ~ In fn (map snd seen) ->
    wellformed Σs 0 body ->
    spec_inv Σs ((k, fn) :: seen)
      ((fn, ConstantDecl {| cst_body :=
           Some (specialize_instances (redirect Σ seen [] body)) |}) :: env).
  Proof.
    intros hext hi hfn hnin hb.
    assert (hfresh : lookup_env env fn = None).
    { destruct (lookup_env env fn) eqn:hl => //.
      destruct (inv_names _ _ _ hi _ _ hl) as [h|h] => //.
      destruct (lookup_env Σs fn) eqn:hl' => //. apply hext in hl'. congruence. }
    split.
    - apply wf_glob_cons; [apply hi| |now apply lookup_None_fresh].
      cbn. now eapply wf_final.
    - intros kn d hl. cbn. destruct (eqb_spec kn fn) as [->|hne].
      + apply hext in hl. congruence.
      + now apply (inv_sim _ _ _ hi).
    - intros fn' hin. cbn in hin. destruct hin as [<-|hin].
      + split => //. unfold lookup_constant. cbn. rewrite eqb_refl. cbn.
        eexists; split; reflexivity.
      + destruct (inv_seen _ _ _ hi _ hin) as [h0 [cb [hc hcb]]]. split => //.
        unfold lookup_constant in *. cbn.
        destruct (eqb_spec fn' fn); [eexists; split; reflexivity|now exists cb].
    - intros kn d. cbn. destruct (eqb_spec kn fn) as [->|hne].
      + intros _. right. now left.
      + intros hl. destruct (inv_names _ _ _ hi _ _ hl); auto.
  Qed.

  (** Keys whose dictionaries and callee body are well-formed in [Σs]. *)
  Definition good_key Σs (k : dkey) : Prop :=
    forallb (wellformed Σs 0) k.2 /\
    forall b, callee_body Σ k.1 = Some b -> wellformed Σs 0 b.

  Lemma wf_const_body Σs k c :
    wf_glob Σs -> extends Σs Σ -> wellformed Σs k (tConst c) ->
    exists cb, lookup_constant Σ c = Some cb /\
               forall b, cst_body cb = Some b -> wellformed Σs 0 b.
  Proof.
    intros hwfs hext. simpl. move/andP => [_]. unfold lookup_constant.
    destruct (lookup_env Σs c) as [d|] eqn:hl => //=. destruct d as [cb|] => //= _.
    rewrite (hext _ _ hl) /=. exists cb; split => // b hb.
    apply lookup_env_wellformed in hl => //. cbn in hl. now rewrite hb in hl.
  Qed.

  Lemma wf_dict_value Σs k t v :
    wf_glob Σs -> extends Σs Σ -> wellformed Σs k t ->
    dict_value Σ t = Some v -> wellformed Σs 0 v.
  Proof.
    intros hwfs hext hw. destruct t; cbn [dict_value] => //.
    - destruct (wf_const_body _ _ _ hwfs hext hw) as [cb [-> hb]].
      destruct (cst_body cb) as [[]|] => //. destruct (_ && _) => //.
      intros [= <-]. now apply hb.
    - destruct (is_record_ind _ _ && _) eqn:h => //. intros [= <-].
      move/andP: h => [_ hc]. eapply wf_closed_down; tea.
  Qed.

  Lemma wf_prefix_elt Σs k t isd v :
    wf_glob Σs -> extends Σs Σ -> wellformed Σs k t ->
    prefix_elt Σ t = Some (isd, v) -> wellformed Σs 0 v.
  Proof.
    intros hwfs hext hw. unfold prefix_elt. destruct dict_value eqn:hd.
    - intros [= _ <-]. eapply wf_dict_value; tea.
    - destruct t => //. intros [= _ <-]. exact hw.
  Qed.

  Lemma wf_split_dicts Σs k spine :
    wf_glob Σs -> extends Σs Σ -> forallb (wellformed Σs k) spine ->
    forallb (wellformed Σs 0) (split_dicts Σ spine).1.2.
  Proof.
    intros hwfs hext. induction spine as [|a spine IH]; cbn [split_dicts] => //.
    move/andP => [ha hs]. destruct (prefix_elt Σ a) as [[isd v]|] eqn:hp => //.
    specialize (IH hs). destruct (split_dicts Σ spine) as [[d' ds] rr]. cbn in *.
    rewrite IH andb_true_r. eapply wf_prefix_elt; tea.
  Qed.

  Lemma mk_key_good Σs k nm spine key rest :
    wf_glob Σs -> extends Σs Σ -> wellformed Σs k (tConst nm) ->
    forallb (wellformed Σs k) spine ->
    mk_key Σ nm spine = Some (key, rest) -> good_key Σs key.
  Proof.
    intros hwfs hext hw hs. unfold mk_key.
    destruct (callee_body Σ nm) as [b|] eqn:hcb => //.
    pose proof (wf_split_dicts _ _ _ hwfs hext hs) as hd.
    destruct (split_dicts Σ spine) as [[d' ds] rr]. destruct d' => //.
    intros [= <- _]. split; [exact hd|]. cbn. intros b'. rewrite hcb. intros [= <-].
    destruct (wf_const_body _ _ _ hwfs hext hw) as [cb [hl hb]].
    apply hb. unfold callee_body in hcb. now rewrite hl in hcb.
  Qed.

  Lemma collect_keys_good Σs :
    wf_glob Σs -> extends Σs Σ ->
    forall t k spine, wellformed Σs k t -> forallb (wellformed Σs k) spine ->
    Forall (good_key Σs) (collect_keys Σ spine t).
  Proof.
    intros hwfs hext.
    induction t using term_forall_list_ind; intros k spine hw hs;
      cbn [collect_keys]; try solve [constructor].
    5:{ destruct mk_key as [[key rest]|] eqn:hk; constructor; [|constructor].
        eapply mk_key_good; tea. }
    4:{ simpl in hw. move/andP: hw => [/andP [_ h1] h2]. apply List.Forall_app; split.
        - now eapply IHt2.
        - eapply IHt1; tea. cbn. now rewrite h2 hs. }
    8:{ simpl in hw. unfold wf_fix_gen, test_def in hw.
        move/andP: hw => [_ /andP [_ hw]].
        apply Forall_concat, Forall_map, All_Forall. solve_all. }
    7:{ simpl in hw. unfold wf_fix_gen, test_def in hw.
        move/andP: hw => [_ /andP [_ hw]].
        apply Forall_concat, Forall_map, All_Forall. solve_all. }
    4:{ apply wf_construct_args in hw.
        apply Forall_concat, Forall_map, All_Forall. solve_all. }
    all: simpl in hw; rtoProp; repeat (apply List.Forall_app; split);
      try (apply Forall_concat, Forall_map, All_Forall); intuition eauto; solve_all.
  Qed.

  Lemma spec_key_inv Σs :
    wf_glob Σs -> extends Σs Σ ->
    forall fuel stack st k, good_key Σs k -> spec_inv Σs st.1.1 st.1.2 ->
    spec_inv Σs (spec_key Σ fuel stack st k).1.1 (spec_key Σ fuel stack st k).1.2.
  Proof.
    intros hwfs hext.
    induction fuel as [|fuel IH]; intros stack [[seen env] budget] k [hd hb] hi;
      cbn [spec_key]; auto.
    destruct budget as [|budget]; auto.
    destruct (_ || _); auto.
    destruct (callee_body Σ k.1) as [b|] eqn:hcb; auto.
    assert (hbody : wellformed Σs 0 (spec_body b k.2))
      by (apply (wf_spec_body (hasapp := hasapp)); auto).
    pose proof (fold_left_inv (fun st => spec_inv Σs st.1.1 st.1.2) (good_key Σs)
                  (spec_key Σ fuel (k :: stack))
                  (collect_keys Σ [] (spec_body b k.2))) as hf.
    forward hf. { intros a c ha hc. now apply IH. }
    forward hf. { now apply (collect_keys_good Σs hwfs hext _ 0). }
    specialize (hf (seen, env, budget) hi).
    destruct fold_left as [[seen' env'] budget'']. cbn in hf.
    destruct fresh_name as [fn|] eqn:hfn; cbn; auto.
    apply fresh_from_spec in hfn as [h1 h2]. now apply spec_inv_add.
  Qed.

  Lemma spec_keys_inv Σs keys seen env :
    wf_glob Σs -> extends Σs Σ ->
    Forall (good_key Σs) keys -> spec_inv Σs seen env ->
    spec_inv Σs (spec_keys Σ keys seen env).1 (spec_keys Σ keys seen env).2.
  Proof.
    intros hwfs hext hk hi. unfold spec_keys.
    apply (fold_left_inv (fun st => spec_inv Σs st.1.1 st.1.2) (good_key Σs)) => //.
    intros a b ha hb. now apply spec_key_inv.
  Qed.

  Lemma drive_decl_inv Σs kd acc :
    wf_glob (kd :: Σs) -> extends (kd :: Σs) Σ -> spec_inv Σs acc.1 acc.2 ->
    spec_inv (kd :: Σs) (drive_decl Σ kd acc).1 (drive_decl Σ kd acc).2.
  Proof.
    intros hwf hext hi. destruct kd as [kn d].
    assert (hwfs : wf_glob Σs) by now depelim hwf.
    assert (hfr : fresh_global kn Σs) by now depelim hwf.
    assert (hd : wf_global_decl Σs d) by now depelim hwf.
    assert (hexts : extends Σs Σ).
    { intros kn' d' hl. apply hext. cbn. destruct (eqb_spec kn' kn) as [->|] => //.
      now apply lookup_env_Some_fresh in hl. }
    assert (hkn : lookup_env Σ kn = Some d). { apply hext. cbn. now rewrite eqb_refl. }
    unfold drive_decl. cbn [fst snd].
    pose proof (spec_keys_inv Σs (body_keys Σ d) acc.1 acc.2 hwfs hexts) as hk.
    forward hk.
    { destruct d as [[[b|]]|]; cbn; try constructor. now apply (collect_keys_good Σs hwfs hexts _ 0). }
    specialize (hk hi). destruct spec_keys as [seen' env']. cbn in hk |- *.
    assert (hfresh : lookup_env env' kn = None).
    { destruct (lookup_env env' kn) eqn:hl => //.
      destruct (inv_names _ _ _ hk _ _ hl) as [h|h].
      - destruct (lookup_env Σs kn) eqn:hl' => //. now apply lookup_env_Some_fresh in hl'.
      - apply (inv_seen _ _ _ hk) in h as [h _]. congruence. }
    split.
    - apply wf_glob_cons; [apply hk| |now apply lookup_None_fresh].
      destruct d as [[[b|]]|]; cbn in hd |- *; auto. now eapply wf_final.
    - intros kn' d' hl. cbn in hl |- *. destruct (eqb_spec kn' kn) as [->|hne].
      + noconf hl. eexists; split; [reflexivity|]. destruct d as [[[b|]]|]; cbn; auto.
      + now apply (inv_sim _ _ _ hk).
    - intros fn hin. destruct (inv_seen _ _ _ hk _ hin) as [h0 [cb [hc hb]]]. split => //.
      unfold lookup_constant in *. cbn.
      destruct (eqb_spec fn kn) as [->|hne]; [congruence|]. now exists cb.
    - intros kn' d'. cbn. destruct (eqb_spec kn' kn) as [->|hne]; [now left|].
      intros hl. now apply (inv_names _ _ _ hk) in hl.
  Qed.

  Lemma drive_fold_inv :
    wf_glob Σ -> forall Σs Σ1, Σ = Σ1 ++ Σs ->
    spec_inv Σs (fold_right (drive_decl Σ) ([], []) Σs).1
                (fold_right (drive_decl Σ) ([], []) Σs).2.
  Proof.
    intros hwf. induction Σs as [|kd Σs IH]; intros Σ1 heq; cbn [fold_right].
    - split; cbn; try easy. constructor.
    - assert (hp : extends_prefix (kd :: Σs) Σ) by (exists Σ1; exact heq).
      apply drive_decl_inv.
      + exact (extends_wf_glob efl hp hwf).
      + exact (extends_prefix_extends efl _ _ hp hwf).
      + apply (IH (Σ1 ++ [kd])). now rewrite -app_assoc.
  Qed.

  Theorem drive_env_wf main :
    wf_glob Σ -> wellformed Σ 0 main ->
    wf_eprogram efl (drive_env Σ main).
  Proof.
    intros hwf hm. unfold wf_eprogram, drive_env.
    pose proof (drive_fold_inv hwf Σ [] eq_refl) as hi.
    set (acc := fold_right _ _ _) in *.
    pose proof (spec_keys_inv Σ (collect_keys Σ [] main) acc.1 acc.2 hwf) as hk.
    forward hk. { now intros ? ? ?. }
    forward hk. { apply (collect_keys_good Σ hwf) with (k := 0) => //. }
    specialize (hk hi). destruct spec_keys as [seen' env']. cbn in *.
    split; [apply hk|]. now eapply wf_final.
  Qed.

End Driver.

Theorem specialize_instances_program_wf {efl : EEnvFlags} {hasapp : has_tApp}
  (p : eprogram) :
  wf_eprogram efl p -> wf_eprogram efl (specialize_instances_program p).
Proof. intros [hwf hm]. now apply (drive_env_wf (hasapp := hasapp)). Qed.

(** ** Transform wrapper (termination assumed) *)

From Peregrine Require Import EExtraFlags.

(** Termination only, at the flags of the pipeline. *)
Axiom trust_specialize_instances_terminates :
  forall (p : Transform.program _ term) (v : term),
  wf_eprogram extra_env_flags p ->
  eval_eprogram extra_wcbv_flags p v ->
  exists v' : term, eval_eprogram extra_wcbv_flags (specialize_instances_program p) v'.

Import Transform.

Program Definition specialize_instances_transformation :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram extra_wcbv_flags) (eval_eprogram extra_wcbv_flags) :=
  {| name := "instance specialization";
     transform p _ := specialize_instances_program p;
     pre p := wf_eprogram extra_env_flags p;
     post p := wf_eprogram extra_env_flags p;
     obseq _ _ _ _ _ := True |}.
Next Obligation.
  intros. now apply (specialize_instances_program_wf (efl := extra_env_flags) (hasapp := eq_refl)).
Qed.
Next Obligation.
  edestruct trust_specialize_instances_terminates as [v' ev]; eauto.
Qed.
