(** Renaming the global names of a λ□ program.

    [rename rk rn] applies [rk] to every kername of a term (constants, and the
    inductive of every constructor, case and projection) and [rn] to every binder
    name; [rename_env] does the same to a global environment, and applies [rs] to
    the names of inductive types, constructors and projections, which no
    reduction rule reads.  If [rk] is injective on the names declared in the
    environment, renaming preserves well-formedness and commutes with weak
    call-by-value evaluation: [eval_rename].  The name sanitization of
    [NameSanitize] is such a renaming ([NameSanitizeCorrect]). *)

From Stdlib Require Import Utf8 Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Kernames BasicAst Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWellformed EWcbvEval EProgram.


Section Rename.
  Context (rk : kername -> kername) (rn : name -> name) (rs : ident -> ident).

  Definition rename_inductive (i : inductive) : inductive :=
    {| inductive_mind := rk i.(inductive_mind); inductive_ind := i.(inductive_ind) |}.

  Definition rename_projection (p : projection) : projection :=
    {| proj_ind := rename_inductive p.(proj_ind);
       proj_npars := p.(proj_npars);
       proj_arg := p.(proj_arg) |}.

  Definition rename_def_with (f : term -> term) (d : def term) : def term :=
    {| dname := rn d.(dname); dbody := f d.(dbody); rarg := d.(rarg) |}.

  Fixpoint rename (t : term) : term :=
    match t with
    | tBox => tBox
    | tRel n => tRel n
    | tVar id => tVar id
    | tEvar ev args => tEvar ev (map rename args)
    | tLambda na M => tLambda (rn na) (rename M)
    | tApp u v => tApp (rename u) (rename v)
    | tLetIn na b b' => tLetIn (rn na) (rename b) (rename b')
    | tCase ind c brs =>
      tCase (rename_inductive ind.1, ind.2) (rename c)
        (map (fun br => (map rn br.1, rename br.2)) brs)
    | tProj p c => tProj (rename_projection p) (rename c)
    | tFix mfix idx => tFix (map (rename_def_with rename) mfix) idx
    | tCoFix mfix idx => tCoFix (map (rename_def_with rename) mfix) idx
    | tConst kn => tConst (rk kn)
    | tConstruct ind n args => tConstruct (rename_inductive ind) n (map rename args)
    | tPrim p => tPrim (map_prim rename p)
    | tLazy u => tLazy (rename u)
    | tForce u => tForce (rename u)
    end.

  Notation rename_def := (rename_def_with rename).
  Definition rename_br (br : list name * term) := (map rn br.1, rename br.2).

  Definition rename_constant_body (cb : constant_body) : constant_body :=
    {| cst_body := option_map rename cb.(cst_body) |}.

  Definition rename_constructor_body (c : constructor_body) : constructor_body :=
    {| cstr_name := rs c.(cstr_name); cstr_nargs := c.(cstr_nargs) |}.

  Definition rename_projection_body (p : projection_body) : projection_body :=
    {| proj_name := rs p.(proj_name) |}.

  Definition rename_one_inductive_body (o : one_inductive_body) : one_inductive_body :=
    {| ind_name := rs o.(ind_name);
       ind_propositional := o.(ind_propositional);
       ind_kelim := o.(ind_kelim);
       ind_ctors := map rename_constructor_body o.(ind_ctors);
       ind_projs := map rename_projection_body o.(ind_projs) |}.

  Definition rename_mutual_inductive_body (m : mutual_inductive_body) : mutual_inductive_body :=
    {| ind_finite := m.(ind_finite);
       ind_npars := m.(ind_npars);
       ind_bodies := map rename_one_inductive_body m.(ind_bodies) |}.

  Definition rename_decl (d : global_decl) : global_decl :=
    match d with
    | ConstantDecl cb => ConstantDecl (rename_constant_body cb)
    | InductiveDecl m => InductiveDecl (rename_mutual_inductive_body m)
    end.

  Definition rename_env (Σ : global_declarations) : global_declarations :=
    map (fun d => (rk d.1, rename_decl d.2)) Σ.

  (** [rk] identifies no two names declared in [Σ]. *)
  Definition injective_on (names : list kername) :=
    forall kn kn', In kn names -> In kn' names -> rk kn = rk kn' -> kn = kn'.

  (** * Syntax *)

  Lemma rename_mkApps f l : rename (mkApps f l) = mkApps (rename f) (map rename l).
  Proof.
    induction l in f |- *; cbn; auto.
  Qed.

  Lemma rename_csubst a k b : rename (csubst a k b) = csubst (rename a) k (rename b).
  Proof.
    induction b in k |- * using term_forall_list_ind; cbn; try reflexivity.
    all: try (destruct (Nat.compare k n); reflexivity).
    all: try solve [f_equal; eauto].
    all: f_equal; eauto; rewrite ?map_map ?length_map; solve_all.
    all: rewrite ?length_map; unfold rename_def_with, map_def; cbn; f_equal; eauto.
  Qed.

  Lemma rename_substl l b : rename (substl l b) = substl (map rename l) (rename b).
  Proof.
    induction l in b |- *; cbn; auto.
    rewrite IHl. f_equal. now rewrite rename_csubst.
  Qed.

  Lemma rename_fix_subst mfix : map rename (fix_subst mfix) = fix_subst (map rename_def mfix).
  Proof.
    unfold fix_subst. rewrite length_map.
    generalize #|mfix|. induction n; cbn; auto. now rewrite IHn.
  Qed.

  Lemma rename_cofix_subst mfix : map rename (cofix_subst mfix) = cofix_subst (map rename_def mfix).
  Proof.
    unfold cofix_subst. rewrite length_map.
    generalize #|mfix|. induction n; cbn; auto. now rewrite IHn.
  Qed.

  Lemma rename_cunfold_fix mfix idx narg fn :
    cunfold_fix mfix idx = Some (narg, fn) ->
    cunfold_fix (map rename_def mfix) idx = Some (narg, rename fn).
  Proof.
    unfold cunfold_fix. rewrite nth_error_map.
    destruct nth_error => //=. intros [= <- <-].
    now rewrite rename_substl rename_fix_subst.
  Qed.

  Lemma rename_cunfold_cofix mfix idx narg fn :
    cunfold_cofix mfix idx = Some (narg, fn) ->
    cunfold_cofix (map rename_def mfix) idx = Some (narg, rename fn).
  Proof.
    unfold cunfold_cofix. rewrite nth_error_map.
    destruct nth_error => //=. intros [= <- <-].
    now rewrite rename_substl rename_cofix_subst.
  Qed.

  Lemma rename_iota_red pars args br :
    rename (iota_red pars args br) = iota_red pars (map rename args) (rename_br br).
  Proof.
    unfold iota_red. rewrite rename_substl. cbn. f_equal.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma rename_decompose_app_rec t l :
    decompose_app_rec (rename t) (map rename l) =
    (rename (decompose_app_rec t l).1, map rename (decompose_app_rec t l).2).
  Proof.
    induction t in l |- *; cbn; auto.
    now rewrite -(IHt1 (t2 :: l)).
  Qed.

  Lemma rename_head t : head (rename t) = rename (head t).
  Proof.
    unfold head, decompose_app.
    have h := rename_decompose_app_rec t []. cbn in h. now rewrite h.
  Qed.

  Lemma isLambda_rename t : isLambda (rename t) = isLambda t.
  Proof. destruct t => //. Qed.

  Lemma isBox_rename t : isBox (rename t) = isBox t.
  Proof. destruct t => //. Qed.

  Lemma isFix_rename t : isFix (rename t) = isFix t.
  Proof. destruct t => //. Qed.

  Lemma isFixApp_rename t : isFixApp (rename t) = isFixApp t.
  Proof. rewrite /isFixApp rename_head. destruct (head t) => //. Qed.

  Lemma isConstructApp_rename t : isConstructApp (rename t) = isConstructApp t.
  Proof. rewrite /isConstructApp rename_head. destruct (head t) => //. Qed.

  Lemma isPrimApp_rename t : isPrimApp (rename t) = isPrimApp t.
  Proof. rewrite /isPrimApp rename_head. destruct (head t) => //. Qed.

  Lemma isLazyApp_rename t : isLazyApp (rename t) = isLazyApp t.
  Proof. rewrite /isLazyApp rename_head. destruct (head t) => //. Qed.

  Lemma rename_repeat_box n : map rename (repeat tBox n) = repeat tBox n.
  Proof. induction n; cbn; auto. now rewrite IHn. Qed.

  (** * Lookups *)

  Lemma lookup_env_In Σ kn d : lookup_env Σ kn = Some d -> In kn (map fst Σ).
    Proof.
      induction Σ as [|[kn' d'] Σ' IH]; cbn => //.
      case: eqb_spec.
      - intros -> _. now left.
      - intros _ h. right. now apply IH.
    Qed.

  Section Env.
    Context (Σ : global_declarations).
    Context (hinj : injective_on (map fst Σ)).

    Lemma lookup_env_rename kn d :
      lookup_env Σ kn = Some d -> lookup_env (rename_env Σ) (rk kn) = Some (rename_decl d).
    Proof.
      induction Σ as [|[kn' d'] Σ' IH] in hinj |- *; cbn => //.
      change (eq_kername ?x ?y) with (eqb x y).
      case: (eqb_spec kn kn').
      - intros -> [= <-]. now rewrite eqb_refl.
      - intros neq h.
        case: (eqb_spec (rk kn) (rk kn')).
        + intros e. exfalso. apply neq. apply hinj; cbn; auto.
          right. eapply lookup_env_In; tea.
        + intros _. apply IH; auto.
          intros x y hx hy. apply hinj; cbn; auto.
    Qed.

    Lemma lookup_constant_rename kn cb :
      lookup_constant Σ kn = Some cb ->
      lookup_constant (rename_env Σ) (rk kn) = Some (rename_constant_body cb).
    Proof.
      rewrite /lookup_constant. destruct (lookup_env Σ _) eqn:h => //=.
      rewrite (lookup_env_rename _ _ h).
      destruct g => //=. now intros [= <-].
    Qed.

    Lemma declared_constant_rename kn cb :
      declared_constant Σ kn cb -> declared_constant (rename_env Σ) (rk kn) (rename_constant_body cb).
    Proof.
      rewrite /declared_constant. intros h. now rewrite (lookup_env_rename _ _ h).
    Qed.

    Lemma lookup_minductive_rename kn m :
      lookup_minductive Σ kn = Some m ->
      lookup_minductive (rename_env Σ) (rk kn) = Some (rename_mutual_inductive_body m).
    Proof.
      rewrite /lookup_minductive. destruct (lookup_env Σ _) eqn:h => //=.
      rewrite (lookup_env_rename _ _ h).
      destruct g => //=. now intros [= <-].
    Qed.

    Lemma lookup_inductive_rename ind m o :
      lookup_inductive Σ ind = Some (m, o) ->
      lookup_inductive (rename_env Σ) (rename_inductive ind) =
        Some (rename_mutual_inductive_body m, rename_one_inductive_body o).
    Proof.
      rewrite /lookup_inductive. destruct (lookup_minductive Σ _) eqn:h => //=.
      rewrite (lookup_minductive_rename _ _ h) /=.
      rewrite nth_error_map. destruct nth_error => //=. now intros [= <- <-].
    Qed.

    Lemma lookup_constructor_rename ind c m o cdecl :
      lookup_constructor Σ ind c = Some (m, o, cdecl) ->
      lookup_constructor (rename_env Σ) (rename_inductive ind) c =
        Some (rename_mutual_inductive_body m, rename_one_inductive_body o,
              rename_constructor_body cdecl).
    Proof.
      rewrite /lookup_constructor. destruct (lookup_inductive Σ _) as [[m' o']|] eqn:h => //=.
      rewrite (lookup_inductive_rename _ _ _ h) /=.
      rewrite nth_error_map. destruct nth_error => //=. now intros [= <- <- <-].
    Qed.

    Lemma isSome_lookup_constructor_rename ind c :
      isSome (lookup_constructor Σ ind c) ->
      isSome (lookup_constructor (rename_env Σ) (rename_inductive ind) c).
    Proof.
      destruct (lookup_constructor Σ _ _) as [[[m o] cd]|] eqn:h => //= _.
      now rewrite (lookup_constructor_rename _ _ _ _ _ h).
    Qed.

    Lemma constructor_isprop_pars_decl_rename ind c b pars cdecl :
      constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) ->
      constructor_isprop_pars_decl (rename_env Σ) (rename_inductive ind) c =
        Some (b, pars, rename_constructor_body cdecl).
    Proof.
      rewrite /constructor_isprop_pars_decl.
      destruct (lookup_constructor Σ _ _) as [[[m o] cd]|] eqn:h => //=.
      rewrite (lookup_constructor_rename _ _ _ _ _ h) /=. now intros [= <- <- <-].
    Qed.

    Lemma inductive_isprop_and_pars_rename ind b pars :
      inductive_isprop_and_pars Σ ind = Some (b, pars) ->
      inductive_isprop_and_pars (rename_env Σ) (rename_inductive ind) = Some (b, pars).
    Proof.
      rewrite /inductive_isprop_and_pars.
      destruct (lookup_inductive Σ _) as [[m o]|] eqn:h => //=.
      rewrite (lookup_inductive_rename _ _ _ h) /=. now intros [= <- <-].
    Qed.

    Lemma lookup_constructor_pars_args_rename ind c p a :
      lookup_constructor_pars_args Σ ind c = Some (p, a) ->
      lookup_constructor_pars_args (rename_env Σ) (rename_inductive ind) c = Some (p, a).
    Proof.
      rewrite /lookup_constructor_pars_args.
      destruct (lookup_constructor Σ _ _) as [[[m o] cd]|] eqn:h => //=.
      now rewrite (lookup_constructor_rename _ _ _ _ _ h) /=.
    Qed.

    Lemma lookup_projection_rename p :
      isSome (lookup_projection Σ p) -> isSome (lookup_projection (rename_env Σ) (rename_projection p)).
    Proof.
      rewrite /lookup_projection.
      destruct (lookup_constructor Σ _ _) as [[[m o] cd]|] eqn:h => //=.
      rewrite (lookup_constructor_rename _ _ _ _ _ h) /=.
      rewrite nth_error_map. now destruct nth_error.
    Qed.

    Lemma atom_rename {wfl : WcbvFlags} t : atom Σ t -> atom (rename_env Σ) (rename t).
    Proof.
      destruct t => //=. destruct args => //=.
      move/andP => [-> h] /=. now apply isSome_lookup_constructor_rename.
    Qed.

  End Env.

  (** * Evaluation *)

  Lemma eval_rename {wfl : WcbvFlags} Σ t v :
    injective_on (map fst Σ) ->
    eval Σ t v -> eval (rename_env Σ) (rename t) (rename v).
  Proof.
    intros hinj ev.
    induction ev using eval_rect; cbn in *.
    - econstructor; eauto.
    - eapply eval_beta; eauto. all: now rewrite -rename_csubst.
    - econstructor; eauto. now rewrite -rename_csubst.
    - rewrite rename_mkApps in IHev1.
      eapply eval_iota; tea.
      + now eapply constructor_isprop_pars_decl_rename.
      + rewrite nth_error_map; match goal with h : nth_error _ _ = Some _ |- _ => now rewrite h end.
      + now rewrite length_map.
      + cbn. now rewrite length_map -map_skipn length_map.
      + now rewrite -rename_iota_red.
    - eapply eval_iota_block; tea.
      + now eapply constructor_isprop_pars_decl_rename.
      + rewrite nth_error_map; match goal with h : nth_error _ _ = Some _ |- _ => now rewrite h end.
      + now rewrite length_map.
      + cbn. now rewrite length_map -map_skipn length_map.
      + now rewrite -rename_iota_red.
    - subst brs. eapply eval_iota_sing; tea.
      + now eapply inductive_isprop_and_pars_rename.
      + reflexivity.
      + cbn. rewrite length_map. rewrite rename_substl rename_repeat_box in IHev2. exact IHev2.
    - rewrite rename_mkApps in IHev1.
      eapply eval_fix; tea.
      + rewrite length_map. now eapply rename_cunfold_fix.
      + now rewrite rename_mkApps in IHev3.
    - rewrite rename_mkApps in IHev1 |- *.
      eapply eval_fix_value; tea.
      + now eapply rename_cunfold_fix.
      + now rewrite length_map.
    - eapply eval_fix'; tea. now eapply rename_cunfold_fix.
    - rewrite rename_mkApps in IHev1.
      eapply eval_cofix_case; tea.
      + now eapply rename_cunfold_cofix.
      + rewrite rename_mkApps in IHev2. exact IHev2.
    - rewrite rename_mkApps in IHev1.
      eapply eval_cofix_proj; tea.
      + now eapply rename_cunfold_cofix.
      + rewrite rename_mkApps in IHev2. exact IHev2.
    - eapply eval_delta.
      + now eapply declared_constant_rename.
      + cbn. now rewrite e.
      + exact IHev.
    - rewrite rename_mkApps in IHev1.
      eapply eval_proj; tea.
      + now eapply (constructor_isprop_pars_decl_rename _ hinj p.(proj_ind) 0).
      + now rewrite length_map.
      + cbn. rewrite nth_error_map; match goal with h : nth_error _ _ = Some _ |- _ => now rewrite h end.
    - eapply eval_proj_block; tea.
      + now eapply (constructor_isprop_pars_decl_rename _ hinj p.(proj_ind) 0).
      + now rewrite length_map.
      + cbn. rewrite nth_error_map; match goal with h : nth_error _ _ = Some _ |- _ => now rewrite h end.
    - eapply eval_proj_prop; tea.
      now eapply (inductive_isprop_and_pars_rename _ hinj p.(proj_ind)).
    - rewrite rename_mkApps in IHev1 |- *.
      eapply eval_construct; tea.
      + now eapply lookup_constructor_rename.
      + now rewrite length_map.
    - eapply eval_construct_block; tea.
      + now eapply lookup_constructor_rename.
      + now rewrite length_map.
      + clear -iha. revert iha. induction a; cbn; intros iha; constructor; destruct iha; auto.
    - eapply eval_app_cong; tea.
      rewrite isLambda_rename isBox_rename isConstructApp_rename isPrimApp_rename
        isLazyApp_rename.
      destruct with_guarded_fix.
      + now rewrite isFixApp_rename.
      + now rewrite isFix_rename.
    - econstructor.
      destruct X; cbn; try constructor.
      + cbn. clear -a. revert a. induction ev; cbn; intros a; constructor; destruct a; auto.
      + exact e.
    - eapply eval_force; tea.
    - eapply eval_atom. now eapply atom_rename.
  Qed.

  (** * Well-formedness *)

  Section Wf.
    Context {efl : EEnvFlags} (Σ : global_declarations).
    Context (hinj : injective_on (map fst Σ)).

    Lemma wellformed_rename k t :
      wellformed Σ k t -> wellformed (rename_env Σ) k (rename t).
    Proof.
      revert k. induction t using term_forall_list_ind; intros k;
        cbn -[lookup_constant lookup_constructor lookup_inductive lookup_projection
              lookup_constructor_pars_args wf_brs] => //; rtoProp; intuition auto.
      all: rewrite ?forallb_map ?length_map.
      all: try solve [solve_all].
      all: try solve [now apply (isSome_lookup_constructor_rename _ hinj)].
      all: try solve [now apply (lookup_projection_rename _ hinj)].
      all: try solve [now rewrite has_prim_map_prim].
      - destruct (lookup_constant Σ s) eqn:h => //.
        rewrite (lookup_constant_rename _ hinj _ _ h) /=. destruct c as [[]] => //.
      - destruct cstr_as_blocks.
        + destruct (lookup_constructor_pars_args Σ i n) as [[p a]|] eqn:h.
          * rewrite (lookup_constructor_pars_args_rename _ hinj _ _ _ _ h).
            rtoProp; intuition auto. solve_all.
          * rtoProp. destruct (lookup_constructor Σ i n) as [[[m o] cd]|] eqn:hl => //.
            move: h; rewrite /lookup_constructor_pars_args hl //.
        + now destruct args.
      - move: H1. rewrite /wf_brs.
        destruct (lookup_inductive Σ p.1) as [[m o]|] eqn:h => //.
        rewrite (lookup_inductive_rename _ hinj _ _ _ h) /= length_map //.
      - cbn. solve_all. rewrite length_map. eauto.
      - solve_all. destruct x as [na [] ra] => //.
      - move: H1. rewrite /wf_fix_gen length_map. move/andP => [-> h] /=.
        rewrite forallb_map. solve_all.
      - move: H1. rewrite /wf_fix_gen length_map. move/andP => [-> h] /=.
        rewrite forallb_map. solve_all.
      - rewrite test_prim_map.
        eapply primProp_impl_test_prim; eapply primProp_impl;
          [eapply primProp_conj; [exact X | eapply test_prim_impl_primProp; exact H1]|].
        cbn. intros x [h1 h2]. now apply h1.
    Qed.

    Lemma wf_minductive_rename m : wf_minductive m -> wf_minductive (rename_mutual_inductive_body m).
    Proof.
      rewrite /wf_minductive /=. move/andP => [-> h] /=.
      rewrite forallb_map. solve_all. move: H. rewrite /wf_inductive /wf_projections /=.
      destruct (ind_projs x) => //=.
      destruct (ind_ctors x) as [|c []] => //=. now rewrite length_map.
    Qed.

  End Wf.

  Lemma injective_on_cons kn names : injective_on (kn :: names) -> injective_on names.
  Proof. intros h x y hx hy. apply h; cbn; auto. Qed.

  Lemma fresh_global_rename kn Σ :
    injective_on (kn :: map fst Σ) -> fresh_global kn Σ -> fresh_global (rk kn) (rename_env Σ).
  Proof.
    rewrite /fresh_global /rename_env !Forall_forall => hinj h x.
    move/in_map_iff => [[k d] [<- hin]] /= e.
    apply (h (k, d) hin). cbn.
    eapply hinj; [right; exact (in_map fst _ _ hin) | now left | exact e].
  Qed.

  Lemma wf_glob_rename {efl : EEnvFlags} Σ :
    injective_on (map fst Σ) -> wf_glob Σ -> wf_glob (rename_env Σ).
  Proof.
    intros hinj wf. induction wf as [|kn d Σ wf IH wfd fresh]; cbn; constructor.
    - apply IH. now eapply injective_on_cons.
    - have hinj' : injective_on (map fst Σ) by now eapply injective_on_cons.
      destruct d; cbn in *.
      + destruct (cst_body c) => //=. now apply wellformed_rename.
      + now apply wf_minductive_rename.
    - now apply fresh_global_rename.
  Qed.

  Lemma wf_eprogram_rename {efl : EEnvFlags} p :
    injective_on (map fst p.1) -> wf_eprogram efl p ->
    wf_eprogram efl (rename_env p.1, rename p.2).
  Proof.
    intros hinj [wfg wft]. split; cbn.
    - now apply wf_glob_rename.
    - now apply wellformed_rename.
  Qed.

End Rename.

(** The renaming as a transformation of programs, with its correctness. *)
Import Transform.

Program Definition rename_transformation {efl : EEnvFlags} {wfl : WcbvFlags}
  (rk : kername -> kername) (rn : BasicAst.name -> BasicAst.name) (rs : ident -> ident) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "rename global names";
     pre p := wf_eprogram efl p /\ injective_on rk (map fst p.1);
     transform p _ := (rename_env rk rn rs p.1, rename rk rn p.2);
     post p := wf_eprogram efl p;
     obseq p _ p' v v' := v' = rename rk rn v |}.
Next Obligation.
  now apply wf_eprogram_rename.
Qed.
Next Obligation.
  destruct pr as [wf hinj]. destruct H as [ev].
  exists (rename rk rn v). split; auto.
  constructor. now apply eval_rename.
Qed.
