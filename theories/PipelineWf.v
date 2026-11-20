(** * Well-formedness through the steps of the middle-end

    The pipeline checks the well-formedness of its input once
    ([Pipeline.check_wf]), before sanitizing names.  The lemmas here carry
    that proof to the input of the transformation pipelines: sanitization is
    an injective renaming ([ERenameGlobals.wf_eprogram_rename]), and dropping
    the bodies of remapped constants turns constants into axioms
    ([wf_glob_drop]). *)

From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EGlobalEnv EWellformed EProgram.
From MetaRocq.Erasure.Typed Require ExAst.
From Peregrine Require Import Utils PAst EExtraFlags ERenameGlobals NameSanitizeCorrect.
From Peregrine Require NameSanitize.

Import ListNotations.

(** *** Dropping constant bodies *)

Definition drop_rel (d' d : global_decl) : Prop :=
  d' = d \/ exists cb, d = ConstantDecl cb /\ d' = ConstantDecl {| cst_body := None |}.

Definition drop_env_rel : global_declarations -> global_declarations -> Prop :=
  Forall2 (fun x y => x.1 = y.1 /\ drop_rel x.2 y.2).

Section DropEnv.
  Context (Σ' Σ : global_declarations) (hrel : drop_env_rel Σ' Σ).

  Lemma lookup_env_drop kn :
    match lookup_env Σ' kn, lookup_env Σ kn with
    | Some d', Some d => drop_rel d' d
    | None, None => True
    | _, _ => False
    end.
  Proof.
    induction hrel as [|[kn1 d1] [kn2 d2] Σ1 Σ2 [e hd] hr IH]; cbn; [exact I|].
    cbn in e, hd. subst kn1. destruct (eqb kn kn2); [exact hd|exact (IH hr)].
  Qed.

  Lemma lookup_minductive_drop kn : lookup_minductive Σ' kn = lookup_minductive Σ kn.
  Proof.
    rewrite /lookup_minductive. pose proof (lookup_env_drop kn) as h.
    destruct (lookup_env Σ' kn), (lookup_env Σ kn) => //.
    destruct h as [->|[cb [-> ->]]]; reflexivity.
  Qed.

  Lemma lookup_inductive_drop ind : lookup_inductive Σ' ind = lookup_inductive Σ ind.
  Proof. now rewrite /lookup_inductive lookup_minductive_drop. Qed.

  Lemma lookup_constructor_drop ind c : lookup_constructor Σ' ind c = lookup_constructor Σ ind c.
  Proof. now rewrite /lookup_constructor lookup_inductive_drop. Qed.

  Lemma lookup_projection_drop p : lookup_projection Σ' p = lookup_projection Σ p.
  Proof. now rewrite /lookup_projection lookup_constructor_drop. Qed.

  Lemma lookup_constructor_pars_args_drop ind c :
    lookup_constructor_pars_args Σ' ind c = lookup_constructor_pars_args Σ ind c.
  Proof. now rewrite /lookup_constructor_pars_args lookup_constructor_drop. Qed.

  Lemma lookup_constant_drop kn :
    isSome (lookup_constant Σ kn) -> isSome (lookup_constant Σ' kn).
  Proof.
    rewrite /lookup_constant. pose proof (lookup_env_drop kn) as h.
    destruct (lookup_env Σ' kn), (lookup_env Σ kn) => //=.
    destruct h as [->|[cb [-> ->]]] => //.
  Qed.

  Lemma map_fst_drop : map fst Σ' = map fst Σ.
  Proof.
    induction hrel as [|x y Σ1 Σ2 [e _] hr IH]; cbn; [reflexivity|]. now rewrite e (IH hr).
  Qed.

  Context {efl : EEnvFlags} (hax : has_axioms = true).

  Lemma wellformed_drop k t :
    @EWellformed.wellformed efl Σ k t -> @EWellformed.wellformed efl Σ' k t.
  Proof.
    revert k. induction t using term_forall_list_ind; intros k;
      cbn -[lookup_constant lookup_constructor lookup_inductive lookup_projection
            lookup_constructor_pars_args wf_brs] => //;
      rewrite ?lookup_constructor_drop ?lookup_projection_drop ?lookup_constructor_pars_args_drop;
      rtoProp; intuition auto.
    all: try solve [solve_all].
    { move: H1. pose proof (lookup_constant_drop s) as h.
      destruct (lookup_constant Σ s), (lookup_constant Σ' s); cbn in h |- *.
      all: intros H; rewrite ?hax //; try discriminate; now specialize (h eq_refl). }
    { destruct cstr_as_blocks => //. rtoProp; intuition auto. solve_all. }
    { move: H1. now rewrite /wf_brs lookup_inductive_drop. }
    { move: H1. rewrite /wf_fix_gen. move/andP => [-> h] /=. solve_all. }
    move: H1. rewrite /wf_fix_gen. move/andP => [-> h] /=. solve_all.
  Qed.

End DropEnv.

Lemma wf_glob_drop {efl : EEnvFlags} (hax : has_axioms = true) Σ' Σ :
  drop_env_rel Σ' Σ -> @wf_glob efl Σ -> @wf_glob efl Σ'.
Proof.
  intros hrel. induction hrel as [|[kn1 d1] [kn2 d2] Σ1 Σ2 [e hd] hrel IH]; intros hwf.
  { constructor. }
  cbn in e, hd. subst kn1. inversion hwf as [|? ? ? hw hdw hf]; subst. constructor.
  { now apply IH. }
  { destruct hd as [->|[cb [-> ->]]].
    { destruct d2 as [[[b|]]|m]; cbn in *; try assumption.
      now apply (wellformed_drop Σ1 Σ2 hrel hax). }
    cbn. now rewrite hax. }
  rewrite /fresh_global in hf *. clear -hf hrel.
  induction hrel as [|x y Σ1 Σ2 [e _] hrel IH]; constructor; inversion hf; subst.
  { now rewrite e. } now apply IH.
Qed.

(** [drop_remapped_bodies] for an arbitrary set of constants. *)
Definition drop_bodies (rem : kername -> bool) (env : ExAst.global_env) : ExAst.global_env :=
  map (fun '(kn, deps, d) =>
    match d with
    | ExAst.ConstantDecl cst =>
      if rem kn
      then (kn, deps, ExAst.ConstantDecl {| ExAst.cst_type := cst.(ExAst.cst_type); ExAst.cst_body := None |})
      else (kn, deps, d)
    | _ => (kn, deps, d)
    end) env.

(** Without remapped constants nothing is dropped. *)
Lemma drop_bodies_none env : drop_bodies (fun _ => false) env = env.
Proof.
  rewrite /drop_bodies. induction env as [|[[kn b] d] env IH]; cbn [map]; [reflexivity|].
  rewrite IH. now destruct d.
Qed.

Lemma drop_env_rel_drop_bodies rem env :
  drop_env_rel (ExAst.trans_env (drop_bodies rem env)) (ExAst.trans_env env).
Proof.
  induction env as [|[[kn b] d] env IH]; cbn; constructor; [|exact IH].
  split; [now destruct d as [cst| |]; [destruct (rem kn)| |]|].
  destruct d as [cst| |]; cbn; [destruct (rem kn); cbn| |]; try (left; reflexivity).
  right. eexists. split; reflexivity.
Qed.

Lemma map_fst_trans_env env : map fst (ExAst.trans_env env) = NameSanitize.typed_env_names env.
Proof. rewrite /ExAst.trans_env /NameSanitize.typed_env_names map_map. reflexivity. Qed.

(** Sanitizing and dropping bodies commute (on the untyped view). *)
Lemma trans_env_drop_sanitize f rem env env_s :
  NameSanitize.sanitize_typed_env f env = Ok env_s ->
  ExAst.trans_env (drop_bodies rem env_s) =
  rename_env (NameSanitize.sanitized_kername f) (sanitized_name f) (sanitized_ident f)
    (ExAst.trans_env (drop_bodies (fun kn => rem (NameSanitize.sanitized_kername f kn)) env)).
Proof.
  intros H. apply sanitize_typed_env_spec in H.
  induction H as [|[[kn b] d] [[kn' b'] d'] env env_s [e1 [e2 hd]] _ IH]; [reflexivity|].
  cbn in e1, e2. subst kn' b'.
  apply sanitize_global_decl_t_spec in hd as [ht hc].
  cbn -[ExAst.trans_global_decl rename_decl]. f_equal; [|exact IH].
  destruct d, d'; cbn in hc; try discriminate.
  all: try (f_equal; exact ht).
  destruct (rem (NameSanitize.sanitized_kername f kn)); [reflexivity|].
  f_equal. exact ht.
Qed.

Lemma map_error_ok {A E E'} (g : E -> E') (r : result A E) a :
  map_error g r = Ok a -> r = Ok a.
Proof. destruct r; cbn; congruence. Qed.


(** *** Well-formed programs of the middle-end *)

(** The untyped view of a parsed program: the untyped environment of typed
    input, and [no_main_term] for a program without a main term, as the
    transformation pipelines get it. *)
Definition PAst_main (t : option term) : term :=
  match t with Some t => t | None => no_main_term end.

Definition PAst_prog (p : PAst) : eprogram :=
  match p with
  | Untyped env t => (env, PAst_main t)
  | Typed env t => (ExAst.trans_env env, PAst_main t)
  end.

(** The precondition of the transformation pipelines, without the
    constructor mapping: what [Pipeline.check_wf] decides. *)
Definition wf_PAst (p : PAst) : Prop := wf_eprogram nocofix_env_flags (PAst_prog p).

Lemma wellformed_no_main_term Σ k : @wellformed nocofix_env_flags Σ k no_main_term.
Proof. reflexivity. Qed.

(** A match on the value of [x] that remembers it ([match with_eq x with
    exist _ v e => ..]). It extracts to [x]. *)
Definition with_eq {A} (x : A) : {y : A | x = y} := @exist A (fun y => x = y) x eq_refl.

Lemma sanitize_option_term_spec f t t' :
  NameSanitize.sanitize_option f NameSanitize.sanitize_term t = Ok t' ->
  t' = option_map (rename (NameSanitize.sanitized_kername f) (sanitized_name f)) t.
Proof.
  destruct t as [t|]; cbn.
  - destruct NameSanitize.sanitize_term as [t1|] eqn:h; cbn; [|discriminate].
    intros [= <-]. now rewrite (sanitize_term_spec f t t1 h).
  - now intros [= <-].
Qed.

(** Sanitization is an injective renaming of the global names, so it
    preserves well-formedness. *)
Lemma sanitize_PAst_wf f p ps :
  injective_on (NameSanitize.sanitized_kername f) (NameSanitize.PAst_names p) ->
  NameSanitize.sanitize_PAst f p = Ok ps -> wf_PAst p -> wf_PAst ps.
Proof.
  set (sk := NameSanitize.sanitized_kername f).
  intros hinj hs hwf.
  destruct p as [env t|env t]; cbn in hs.
  - destruct NameSanitize.sanitize_untyped_env as [env1|] eqn:he; cbn in hs; [|discriminate].
    destruct NameSanitize.sanitize_option as [t1|] eqn:ht; cbn in hs; [|discriminate].
    injection hs as <-.
    apply sanitize_untyped_env_spec in he. apply sanitize_option_term_spec in ht. subst env1 t1.
    have [hg ht] := wf_eprogram_rename sk (sanitized_name f) (sanitized_ident f) (env, PAst_main t) hinj hwf.
    cbn in hg, ht.
    destruct t as [t|]; cbn in *; split; auto; apply wellformed_no_main_term.
  - destruct NameSanitize.sanitize_typed_env as [env1|] eqn:he; cbn in hs; [|discriminate].
    destruct NameSanitize.sanitize_option as [t1|] eqn:ht; cbn in hs; [|discriminate].
    injection hs as <-.
    apply sanitize_option_term_spec in ht. subst t1.
    have heq := trans_env_drop_sanitize f (fun _ => false) env env1 he.
    rewrite !drop_bodies_none in heq.
    have hinj' : injective_on sk (map fst (ExAst.trans_env env)) by rewrite map_fst_trans_env.
    have [hg ht] := wf_eprogram_rename sk (sanitized_name f) (sanitized_ident f)
                      (ExAst.trans_env env, PAst_main t) hinj' hwf.
    cbn in hg, ht. rewrite /wf_PAst /PAst_prog heq.
    destruct t as [t|]; cbn in *; split; auto; apply wellformed_no_main_term.
Qed.

(** Dropping constant bodies preserves well-formedness. *)
Lemma wf_eprogram_drop_bodies rem env t :
  wf_eprogram nocofix_env_flags (ExAst.trans_env env, t) ->
  wf_eprogram nocofix_env_flags (ExAst.trans_env (drop_bodies rem env), t).
Proof.
  intros [hg ht]. have hrel := drop_env_rel_drop_bodies rem env.
  split.
  - exact (wf_glob_drop (efl := nocofix_env_flags) eq_refl _ _ hrel hg).
  - exact (wellformed_drop _ _ hrel (efl := nocofix_env_flags) eq_refl 0 t ht).
Qed.
