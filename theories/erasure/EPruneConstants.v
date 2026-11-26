(** * Pruning of the constants unreachable from the main term

    Instance specialization ([EInstanceSpecialize]) keeps the constants it
    cloned, and nothing else removes a constant that the program no longer
    uses.  [prune_program] keeps the constants reachable from the main term
    ([term_global_deps]) and every inductive.  The environment is
    newest-first and a declaration refers only to older ones, so one pass from
    the newest declaration computes reachability.  A program without a main
    term, whose main is [tBox], is a library: every constant is kept.

    Correctness, without axioms:
    - [prune_program_wf]: well-formedness is preserved, for any flags;
    - [prune_program_eval]: the pruned program evaluates to the same value.
    The latter rests on [eval_strengthen]: an evaluation in [Σ] of a term
    well-formed in a well-formed [Σ'] that [Σ] extends and that has the same
    inductives is an evaluation in [Σ']. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWellformed EWcbvEval EProgram.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

Import ListNotations.
Set Default Proof Using "Type*".

Definition decl_global_deps (d : global_decl) : KernameSet.t :=
  match d with
  | ConstantDecl {| cst_body := Some b |} => term_global_deps b
  | _ => KernameSet.empty
  end.

(** [live] holds the constants used by the newer declarations and the main
    term.  A constant is kept when it is live; its dependencies are then live
    for the older declarations. *)
Fixpoint prune_decls (live : KernameSet.t) (Σ : global_declarations) : global_declarations :=
  match Σ with
  | [] => []
  | (kn, d) :: Σ =>
    match d with
    | InductiveDecl _ => (kn, d) :: prune_decls live Σ
    | ConstantDecl _ =>
      if KernameSet.mem kn live
      then (kn, d) :: prune_decls (KernameSet.union (decl_global_deps d) live) Σ
      else prune_decls live Σ
    end
  end.

Definition prune_env (Σ : global_declarations) (main : term) : global_declarations :=
  match main with
  | tBox => Σ
  | _ => prune_decls (term_global_deps main) Σ
  end.

Definition prune_program (p : global_declarations × term) : global_declarations × term :=
  (prune_env p.1 p.2, p.2).

Example prune_keeps_reachable :
  let k (s : string) : kername := (MPfile ["T"%bs], s) in
  prune_env [(k "c", ConstantDecl {| cst_body := Some (tConst (k "a")) |});
             (k "b", ConstantDecl {| cst_body := Some tBox |});
             (k "a", ConstantDecl {| cst_body := None |})] (tConst (k "c"))
  = [(k "c", ConstantDecl {| cst_body := Some (tConst (k "a")) |});
     (k "a", ConstantDecl {| cst_body := None |})].
Proof. vm_compute. reflexivity. Qed.

Example prune_library (Σ : global_declarations) : prune_env Σ tBox = Σ.
Proof. reflexivity. Qed.

(** ** The pruned environment *)

Lemma prune_decls_Forall (P : kername × global_decl -> Prop) live Σ :
  Forall P Σ -> Forall P (prune_decls live Σ).
Proof.
  induction 1 as [|[kn d] Σ hp hΣ IH] in live |- *; cbn; [constructor|].
  destruct d; [destruct KernameSet.mem|]; auto.
Qed.

Lemma lookup_env_Some_In Σ kn d : lookup_env Σ kn = Some d -> In kn (map fst Σ).
Proof.
  induction Σ as [|[kn' d'] Σ IH]; cbn; [discriminate|].
  destruct (eqb_spec kn kn'); [intros _; left; auto|intros h; right; auto].
Qed.

Lemma fresh_global_lookup kn Σ : fresh_global kn Σ -> lookup_env Σ kn = None.
Proof.
  unfold fresh_global. induction 1 as [|[kn' d'] Σ hne _ IH]; cbn in *; auto.
  destruct (eqb_spec kn kn'); [congruence|auto].
Qed.

Section Lookup.
  Context {efl : EEnvFlags}.

  (** The pruned environment is extended by the source. *)
  Lemma prune_decls_sub Σ live kn d :
    wf_glob Σ -> lookup_env (prune_decls live Σ) kn = Some d -> lookup_env Σ kn = Some d.
  Proof.
    intros wf. induction wf as [|kn0 d0 Σ wf IH hd hfr] in live |- *; cbn; [discriminate|].
    destruct d0 as [cb|mb]; [destruct KernameSet.mem|]; cbn.
    - destruct (eqb_spec kn kn0); auto. intros h. eapply IH; exact h.
    - intros h. apply IH in h as h'. destruct (eqb_spec kn kn0); auto. subst.
      now rewrite fresh_global_lookup in h'.
    - destruct (eqb_spec kn kn0); auto. intros h. eapply IH; exact h.
  Qed.

  (** A live constant and every inductive keep their declaration. *)
  Lemma prune_decls_keep Σ live kn d :
    lookup_env Σ kn = Some d ->
    (KernameSet.In kn live \/ exists m, d = InductiveDecl m) ->
    lookup_env (prune_decls live Σ) kn = Some d.
  Proof.
    induction Σ as [|[kn0 d0] Σ IH] in live |- *; cbn; [discriminate|].
    destruct (eqb_spec kn kn0) as [->|hne].
    - intros [= ->] hk. destruct d as [cb|mb].
      + destruct hk as [hk|[m hm]]; [|discriminate].
        apply KernameSet.mem_spec in hk. rewrite hk. cbn. now rewrite eqb_refl.
      + cbn. now rewrite eqb_refl.
    - intros hl hk. assert (hne' : (kn == kn0) = false) by (destruct (eqb_spec kn kn0); [contradiction|reflexivity]).
      destruct d0 as [cb|mb]; [destruct KernameSet.mem|]; cbn; rewrite ?hne'.
      + apply IH; auto. destruct hk as [hk|hk]; [left|right; auto].
        apply KernameSet.union_spec. now right.
      + now apply IH.
      + now apply IH.
  Qed.

  Lemma prune_decls_live Σ live kn :
    wf_glob Σ -> KernameSet.In kn live ->
    lookup_env (prune_decls live Σ) kn = lookup_env Σ kn.
  Proof.
    intros wf hk. destruct (lookup_env Σ kn) eqn:E.
    - apply prune_decls_keep; auto.
    - destruct (lookup_env (prune_decls live Σ) kn) eqn:E'; auto.
      apply prune_decls_sub in E'; auto. congruence.
  Qed.

  Lemma prune_decls_minductive Σ live kn :
    wf_glob Σ -> lookup_minductive (prune_decls live Σ) kn = lookup_minductive Σ kn.
  Proof.
    intros wf. unfold lookup_minductive.
    destruct (lookup_env Σ kn) as [[cb|mb]|] eqn:E.
    - destruct (lookup_env (prune_decls live Σ) kn) eqn:E'; cbn; auto.
      apply prune_decls_sub in E'; auto. rewrite E in E'. now injection E' as <-.
    - rewrite (prune_decls_keep Σ live kn (InductiveDecl mb)); eauto.
    - destruct (lookup_env (prune_decls live Σ) kn) eqn:E'; cbn; auto.
      apply prune_decls_sub in E'; auto. congruence.
  Qed.

End Lookup.

(** ** Well-formedness of a term depends only on its dependencies *)

Section Transfer.
  Context {efl : EEnvFlags}.
  Variables Σ Σ' : global_declarations.
  Hypothesis Hind : forall kn, lookup_minductive Σ' kn = lookup_minductive Σ kn.

  Lemma transfer_lookup_inductive ind : lookup_inductive Σ' ind = lookup_inductive Σ ind.
  Proof. unfold lookup_inductive. now rewrite Hind. Qed.

  Lemma transfer_lookup_constructor ind c :
    lookup_constructor Σ' ind c = lookup_constructor Σ ind c.
  Proof. unfold lookup_constructor. now rewrite transfer_lookup_inductive. Qed.

  Lemma transfer_lookup_projection p : lookup_projection Σ' p = lookup_projection Σ p.
  Proof. unfold lookup_projection. now rewrite transfer_lookup_constructor. Qed.

  Lemma transfer_lookup_constructor_pars_args ind c :
    lookup_constructor_pars_args Σ' ind c = lookup_constructor_pars_args Σ ind c.
  Proof. unfold lookup_constructor_pars_args. now rewrite transfer_lookup_constructor. Qed.

  Lemma transfer_wf_brs ind n : wf_brs Σ' ind n = wf_brs Σ ind n.
  Proof. unfold wf_brs. now rewrite transfer_lookup_inductive. Qed.

  Hypothesis noevar : has_tEvar = false.

  Lemma forallb_transfer {A} (P : A -> Type) (p q : A -> bool) l :
    All P l -> (forall a, In a l -> P a -> p a -> q a) -> forallb p l -> forallb q l.
  Proof.
    induction 1 as [|a l pa al IH]; cbn; auto.
    intros h. move/andP => [ha hl]. apply/andP; split.
    - apply h; auto; now left.
    - apply IH; auto.
  Qed.

  Lemma in_fold_deps {A} (f : A -> term) l acc a kn :
    In a l -> KernameSet.In kn (term_global_deps (f a)) ->
    KernameSet.In kn (fold_left (fun acc x => KernameSet.union (term_global_deps (f x)) acc) l acc).
  Proof.
    intros hin hk. apply (knset_in_fold_left kn (fun x => term_global_deps (f x))). right. now exists a.
  Qed.

  Lemma in_fold_acc {A} (g : A -> KernameSet.t) l acc kn :
    KernameSet.In kn acc ->
    KernameSet.In kn (fold_left (fun acc x => KernameSet.union (g x) acc) l acc).
  Proof. intros hk. apply knset_in_fold_left. now left. Qed.

  Lemma wellformed_transfer t k :
    (forall kn, KernameSet.In kn (term_global_deps t) -> lookup_env Σ' kn = lookup_env Σ kn) ->
    wellformed Σ k t -> wellformed Σ' k t.
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; intros hdeps hwf;
      cbn [wellformed term_global_deps] in hwf, hdeps |- *; auto.
    all: rewrite ?transfer_lookup_projection ?transfer_lookup_constructor
                 ?transfer_lookup_constructor_pars_args ?transfer_wf_brs; auto.
    all: rtoProp; intuition auto.
    all: try solve [eapply IHt; eauto; intros kn h; apply hdeps; apply KernameSet.union_spec; auto].
    all: try solve [eapply IHt1; eauto; intros kn h; apply hdeps; apply KernameSet.union_spec; auto].
    all: try solve [eapply IHt2; eauto; intros kn h; apply hdeps; apply KernameSet.union_spec; auto].
    - (* tEvar *) rewrite noevar in H; discriminate.
    - (* tConst *) unfold lookup_constant in *. rewrite hdeps //. now apply KernameSet.singleton_spec.
    - (* tConstruct *) destruct i as [mind ii]. cbn [term_global_deps] in hdeps.
      destruct cstr_as_blocks; rtoProp; intuition auto.
      eapply forallb_transfer; tea. intros a hin ha. apply ha.
      intros kn hk; apply hdeps. now eapply (in_fold_deps id).
    - (* tCase *) destruct p as [ind npar]. cbn [term_global_deps] in hdeps.
      + eapply IHt; eauto. intros kn h; apply hdeps; apply KernameSet.union_spec; right.
        now apply in_fold_acc.
    - destruct p as [ind npar]. cbn [term_global_deps] in hdeps.
      eapply forallb_transfer; tea. intros a hin ha. apply ha.
      intros kn hk; apply hdeps. apply KernameSet.union_spec; right. now eapply (in_fold_deps snd).
    - (* tFix *) unfold wf_fix_gen in *. rtoProp; intuition auto.
      eapply forallb_transfer; tea. intros a hin ha. unfold test_def. apply ha.
      intros kn hk; apply hdeps. now eapply (in_fold_deps dbody).
    - (* tCoFix *) unfold wf_fix_gen in *. rtoProp; intuition auto.
      eapply forallb_transfer; tea. intros a hin ha. unfold test_def. apply ha.
      intros kn hk; apply hdeps. now eapply (in_fold_deps dbody).
    - (* tPrim *) depelim X; cbn in *; auto.
      destruct p as [hd hv]. unfold test_array_model in *. rtoProp; split.
      + apply hd; auto. intros kn hk; apply hdeps. simp prim_global_deps. now apply in_fold_acc.
      + eapply forallb_transfer; tea. intros y hin hy. apply hy.
        intros kn hk; apply hdeps. simp prim_global_deps. now eapply (in_fold_deps id).
  Qed.

End Transfer.

(** ** Well-formedness *)

Section Wf.
  Context {efl : EEnvFlags}.
  Hypothesis noevar : has_tEvar = false.

  Lemma prune_decls_wf Σ live : wf_glob Σ -> wf_glob (prune_decls live Σ).
  Proof.
    intros wf. induction wf as [|kn d Σ wf IH hd hfr] in live |- *; cbn; [constructor|].
    destruct d as [cb|mb]; [destruct KernameSet.mem eqn:hm|].
    - constructor; auto.
      + destruct cb as [[b|]]; cbn in hd |- *; auto.
        eapply wellformed_transfer; tea.
        * intros kn'. now apply prune_decls_minductive.
        * intros kn' hk. apply prune_decls_live; auto. apply KernameSet.union_spec. now left.
      + now apply prune_decls_Forall.
    - auto.
    - constructor; auto. now apply prune_decls_Forall.
  Qed.

  Lemma wellformed_prune_decls Σ live k t :
    wf_glob Σ ->
    KernameSet.Subset (term_global_deps t) live ->
    wellformed Σ k t -> wellformed (prune_decls live Σ) k t.
  Proof.
    intros wf hs. eapply wellformed_transfer; tea.
    - intros kn. now apply prune_decls_minductive.
    - intros kn hk. apply prune_decls_live; auto.
  Qed.

  Theorem prune_program_wf p : wf_eprogram efl p -> wf_eprogram efl (prune_program p).
  Proof.
    destruct p as [Σ t]. intros [wf hw]. unfold prune_program, prune_env; cbn [fst snd] in *.
    destruct t; try (split; [now apply prune_decls_wf|now apply wellformed_prune_decls]).
    now split.
  Qed.

End Wf.

(** ** Evaluation in a smaller environment *)

Section Strengthen.
  Context {efl : EEnvFlags} {wfl : WcbvFlags} (hasapp : has_tApp).
  Variables Σ Σ' : global_declarations.
  Hypothesis wf' : wf_glob Σ'.
  Hypothesis ext : extends Σ' Σ.
  Hypothesis Hind : forall kn, lookup_minductive Σ' kn = lookup_minductive Σ kn.

  Lemma strengthen_constructor_isprop_pars_decl ind c :
    constructor_isprop_pars_decl Σ' ind c = constructor_isprop_pars_decl Σ ind c.
  Proof. unfold constructor_isprop_pars_decl. now rewrite (transfer_lookup_constructor Σ Σ'). Qed.

  Lemma strengthen_inductive_isprop_and_pars ind :
    inductive_isprop_and_pars Σ' ind = inductive_isprop_and_pars Σ ind.
  Proof. unfold inductive_isprop_and_pars. now rewrite (transfer_lookup_inductive Σ Σ'). Qed.

  Lemma strengthen_atom t : atom Σ' t = atom Σ t.
  Proof. unfold atom. destruct t; try reflexivity. destruct args; try reflexivity. now rewrite (transfer_lookup_constructor Σ Σ' Hind). Qed.

  Lemma strengthen_declared_constant c decl :
    declared_constant Σ c decl -> wellformed Σ' 0 (tConst c) -> declared_constant Σ' c decl.
  Proof.
    unfold declared_constant. cbn. unfold lookup_constant.
    intros hd. destruct (lookup_env Σ' c) as [[d|]|] eqn:E; rewrite ?andb_false_r //.
    intros _. apply ext in E. congruence.
  Qed.

  Let wfv t v : eval Σ' t v -> wellformed Σ' 0 t -> wellformed Σ' 0 v :=
    fun ev hw => eval_wellformed Σ' hasapp wf' t v hw ev.


  Lemma wf_construct_args ind c args :
    wellformed Σ' 0 (tConstruct ind c args) -> forallb (wellformed Σ' 0) args.
  Proof.
    cbn. move/andP => [_ h]. destruct cstr_as_blocks.
    - now move/andP: h => [_ h].
    - destruct args; [reflexivity|discriminate].
  Qed.

  Lemma eval_strengthen t v : eval Σ t v -> wellformed Σ' 0 t -> eval Σ' t v.
  Proof.
    induction 1 as [] using eval_ind; intros hwf.
    - (* box *) move: hwf => /= /andP[/andP[_ hf] ha]. econstructor; eauto.
    - (* beta *) move: hwf => /= /andP[/andP[_ hf] ha].
      have ev1 := IHeval1 hf. have w1 := wfv _ _ ev1 hf.
      have ev2 := IHeval2 ha. have w2 := wfv _ _ ev2 ha.
      econstructor; tea. apply IHeval3. eapply wellformed_csubst; tea.
      move: w1 => /= /andP[_ w1] //.
    - (* zeta *) move: hwf => /= /andP[/andP[_ h0] h1].
      have ev1 := IHeval1 h0. have w1 := wfv _ _ ev1 h0.
      econstructor; tea. apply IHeval2. eapply wellformed_csubst; tea.
    - (* iota *) move: hwf => /= /andP[_ /andP[/andP[_ hd] hbrs]].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      rewrite wellformed_mkApps // in w1. move/andP: w1 => [_ wargs].
      eapply eval_iota; tea. rewrite strengthen_constructor_isprop_pars_decl; tea.
      apply IHeval2. eapply wellformed_iota_red_brs; tea.
    - (* iota block *) move: hwf => /= /andP[_ /andP[/andP[_ hd] hbrs]].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      have wargs := wf_construct_args _ _ _ w1.
      eapply eval_iota_block; tea. rewrite strengthen_constructor_isprop_pars_decl; tea.
      apply IHeval2. eapply wellformed_iota_red_brs; tea.
    - (* iota sing *) move: hwf => /= /andP[_ /andP[/andP[_ hd] hbrs]].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      eapply eval_iota_sing; tea. rewrite strengthen_inductive_isprop_and_pars; tea.
      apply IHeval2. subst brs. eapply wellformed_substl.
      + eapply All_forallb, All_repeat. exact w1.
      + rewrite repeat_length. cbn in hbrs. now move/andP: hbrs => [h _].
    - (* fix *) move: hwf => /= /andP[/andP[hap hf] ha].
      have ev1 := IHeval1 hf. have w1 := wfv _ _ ev1 hf.
      have ev2 := IHeval2 ha. have w2 := wfv _ _ ev2 ha.
      rewrite wellformed_mkApps // in w1. move/andP: w1 => [wfix wargs].
      eapply eval_fix; tea. apply IHeval3. cbn [wellformed].
      rewrite hap w2 andb_true_r /= wellformed_mkApps // wargs andb_true_r.
      eapply wellformed_cunfold_fix; tea.
    - (* fix value *) move: hwf => /= /andP[/andP[_ hf] ha]. eapply eval_fix_value; eauto.
    - (* fix' *) move: hwf => /= /andP[/andP[hap hf] ha].
      have ev1 := IHeval1 hf. have w1 := wfv _ _ ev1 hf.
      have ev2 := IHeval2 ha. have w2 := wfv _ _ ev2 ha.
      eapply eval_fix'; tea. apply IHeval3. cbn [wellformed].
      rewrite hap w2 andb_true_r /=. eapply wellformed_cunfold_fix; tea.
    - (* cofix case *) move: hwf => /= /andP[hc /andP[/andP[hb hd] hbrs]].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      rewrite wellformed_mkApps // in w1. move/andP: w1 => [wfix wargs].
      eapply eval_cofix_case; tea. apply IHeval2. cbn [wellformed].
      rewrite hc hb hbrs /= andb_true_r wellformed_mkApps // wargs andb_true_r.
      eapply wellformed_cunfold_cofix; tea.
    - (* cofix proj *) move: hwf => /= /andP[/andP[hp hl] hd].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      rewrite wellformed_mkApps // in w1. move/andP: w1 => [wfix wargs].
      eapply eval_cofix_proj; tea. apply IHeval2. cbn [wellformed].
      rewrite hp hl /= wellformed_mkApps // wargs andb_true_r.
      eapply wellformed_cunfold_cofix; tea.
    - (* delta *) have hd' := strengthen_declared_constant _ _ isdecl hwf.
      eapply eval_delta; tea. apply IHeval.
      move: (lookup_env_wellformed wf' hd'). rewrite /wf_global_decl e //.
    - (* proj *) move: hwf => /= /andP[/andP[hp hl] hd].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      rewrite wellformed_mkApps // in w1. move/andP: w1 => [_ wargs].
      eapply eval_proj; tea. rewrite strengthen_constructor_isprop_pars_decl; tea.
      apply IHeval2. eapply nth_error_forallb in wargs; tea.
    - (* proj block *) move: hwf => /= /andP[/andP[hp hl] hd].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      have wargs := wf_construct_args _ _ _ w1.
      eapply eval_proj_block; tea. rewrite strengthen_constructor_isprop_pars_decl; tea.
      apply IHeval2. eapply nth_error_forallb in wargs; tea.
    - (* proj prop *) move: hwf => /= /andP[/andP[hp hl] hd].
      eapply eval_proj_prop; eauto. rewrite strengthen_inductive_isprop_and_pars; tea.
    - (* construct *) move: hwf => /= /andP[/andP[_ hf] ha].
      eapply eval_construct; eauto. rewrite (transfer_lookup_constructor Σ Σ' Hind); tea.
    - (* construct block *) have hargs := wf_construct_args _ _ _ hwf.
      eapply eval_construct_block; tea. rewrite (transfer_lookup_constructor Σ Σ' Hind); tea.
      clear -iha hargs. induction a; constructor.
      + destruct iha as [ih _]. apply ih. now move/andP: hargs => [h _].
      + destruct iha as [_ ih]. apply IHa; auto. now move/andP: hargs => [_ h].
    - (* app cong *) move: hwf => /= /andP[/andP[_ hf] ha]. eapply eval_app_cong; eauto.
    - (* prim *) apply eval_prim. depelim X; [constructor|constructor|constructor|].
      move: hwf => /= /andP[_ hw]. cbn in hw. move/andP: hw => [hd hv]. constructor.
      + subst a0; cbn in hv. clear -a hv. induction ev; constructor.
        * destruct a as [ih _]. apply ih. now move/andP: hv => [h _].
        * destruct a as [_ ih]. apply IHev; auto. now move/andP: hv => [_ h].
      + now apply e.
    - (* force *) move: hwf => /= /andP[_ hd].
      have ev1 := IHeval1 hd. have w1 := wfv _ _ ev1 hd.
      eapply eval_force; tea. apply IHeval2. now move: w1 => /= /andP[_ w1].
    - (* atom *) apply eval_atom. now rewrite strengthen_atom.
  Qed.

End Strengthen.

(** ** Whole programs *)

Lemma prune_decls_eval {efl : EEnvFlags} {wfl : WcbvFlags} (hasapp : has_tApp)
  (noevar : has_tEvar = false) Σ live t v :
  wf_glob Σ -> wellformed Σ 0 t -> KernameSet.Subset (term_global_deps t) live ->
  eval Σ t v -> eval (prune_decls live Σ) t v.
Proof.
  intros wf hw hs ev. eapply eval_strengthen; tea.
  - now apply prune_decls_wf.
  - intros kn d. now apply prune_decls_sub.
  - intros kn. now apply prune_decls_minductive.
  - now apply wellformed_prune_decls.
Qed.

Theorem prune_program_eval {efl : EEnvFlags} {wfl : WcbvFlags} (hasapp : has_tApp)
  (noevar : has_tEvar = false) (p : eprogram) (v : term) :
  wf_eprogram efl p -> eval_eprogram wfl p v -> eval_eprogram wfl (prune_program p) v.
Proof.
  destruct p as [Σ t]. intros [wf hw] [ev]. unfold prune_program, prune_env; cbn [fst snd] in *.
  destruct t; try (now sq).
  all: sq; apply prune_decls_eval; auto; intros kn h; exact h.
Qed.

From MetaRocq.Common Require Import Transform.
Import Transform.

Program Definition prune_transformation (efl : EEnvFlags) (wfl : WcbvFlags)
  (hasapp : has_tApp) (noevar : has_tEvar = false) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "pruning unreachable constants";
     transform p _ := prune_program p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  now apply prune_program_wf.
Qed.
Next Obligation.
  exists v. split; [now eapply prune_program_eval|reflexivity].
Qed.
