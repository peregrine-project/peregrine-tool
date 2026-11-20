(** * First-order results from the input file to the lambda-box program

    [peregrine_middle_end] is the part of [peregrine_pipeline_ast] up to the hand-off
    to the backend: it returns the (sanitized) configuration and the lambda-box
    program that [check_lowered] and [run_backend] get.  [peregrine_pipeline]
    factors through it ([peregrine_pipeline_middle_end]).

    Everything here is generic in the implementation [guard] of the guard
    condition that MetaRocq's pipelines take as a parameter: the results are
    about [peregrine_pipeline_gen], and hold in particular for the executable
    [peregrine_pipeline], its instance at MetaRocq's [fake_guard_impl]
    ([peregrine_pipeline_instance]).  They do not depend on the axiom
    [Erasure.fake_guard_impl_properties] about that instance.

    The corollaries at the end compose the parser ([PipelineParse]), the name
    sanitization ([NameSanitizeCorrect]) and the first-order results of the
    transformation pipelines ([EFirstOrderCorrect], [EFirstOrderTyped]): if the
    input file is the serialization of a program that evaluates to a saturated
    first-order value, the lambda-box program handed to the backend evaluates to
    the translated value.  Covered: untyped input with an untyped backend, typed
    input with an untyped or a typed backend.  Not covered: untyped input with a
    typed backend (the type inference [infer_for_backend] has no correctness
    result). *)

From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.SafeChecker Require PCUICWfEnvImpl.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts CheckWf RecursorInlining AutoInlining
  Pipeline PipelineParse.
From Peregrine Require NameSanitize.
From Peregrine Require Import Utils.
From Peregrine Require Import Serialize SerializeRoundtrip SerializeConfig SerializePAst.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EGlobalEnv EWellformed EProgram EWcbvEval.
From MetaRocq.Erasure.Typed Require ExAst.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ERenameGlobals Transforms EFirstOrder EFirstOrderEta
  EFirstOrderCorrect EFirstOrderTyped NameSanitizeCorrect PipelineWf.

Import MonadNotation.
Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** ** The middle-end *)

Definition peregrine_middle_end {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (p : PAst) : result' (config * PAst) :=
  cp <- peregrine_front c attrs inline_recursors inl p;;
  let c := (proj1_sig cp).1 in
  p <- apply_transforms c lbox (proj1_sig cp).2 (needs_typed c) (proj2_sig cp);;
  Ok (c, p).

(** The backend part of the pipeline. *)
Definition peregrine_backend (c : config) (p : PAst) (f : string) : extraction_result :=
  check_lowered c p;;
  run_backend c f p.

Definition peregrine_middle_end_string {guard : PCUICWfEnvImpl.abstract_guard_impl}
  (c : string + config') (attrs : list string) (inline_recursors : bool)
  (inl : inline_opts) (lbox : lbox_opts) (s : string) : result' (config * PAst) :=
  p <- parse_ast s;;
  peregrine_middle_end c attrs inline_recursors inl lbox p.

Lemma peregrine_pipeline_ast_middle_end {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox p f :
  peregrine_pipeline_ast c attrs ir io lbox p f =
  (r <- peregrine_middle_end c attrs ir io lbox p;; peregrine_backend r.1 r.2 f).
Proof.
  unfold peregrine_pipeline_ast, peregrine_middle_end, peregrine_backend, peregrine_back.
  destruct peregrine_front as [[[c1 p1] h]|e]; cbn; [|reflexivity].
  destruct apply_transforms; cbn; reflexivity.
Qed.

(** [peregrine_pipeline] is the middle-end followed by the backend. *)
Theorem peregrine_pipeline_middle_end {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox s f :
  peregrine_pipeline_gen c attrs ir io lbox s f =
  (r <- peregrine_middle_end_string c attrs ir io lbox s;; peregrine_backend r.1 r.2 f).
Proof.
  unfold peregrine_middle_end_string. destruct (parse_ast s) as [p|e] eqn:E; cbn.
  { rewrite (peregrine_pipeline_parsed c attrs ir io lbox s f p E). apply peregrine_pipeline_ast_middle_end. }
  now apply peregrine_pipeline_parse_error.
Qed.

Lemma peregrine_middle_end_string_of_PAst {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox (p0 : PAst) :
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) =
  peregrine_middle_end c attrs ir io lbox p0.
Proof.
  intros H. unfold peregrine_middle_end_string. now rewrite parse_ast_string_of_PAst.
Qed.

Lemma sanitize_config_backend f c c' :
  NameSanitize.sanitize_config f c = Ok c' -> c'.(backend_opts) = c.(backend_opts).
Proof.
  unfold NameSanitize.sanitize_config. cbn.
  do 5 (destruct monad_map; cbn; [|discriminate]).
  now intros [= <-].
Qed.

Lemma peregrine_middle_end_inv {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox p c' p' :
  peregrine_middle_end c attrs ir io lbox p = Ok (c', p') ->
  exists c1 ps,
    NameSanitize.get_sanitizer c' = NameSanitize.get_sanitizer c1 /\
    check_wf p = Ok tt /\
    NameSanitize.check_sanitized_injective (NameSanitize.get_sanitizer c1)
      (NameSanitize.PAst_names p ++ NameSanitize.config_names c1) = Ok tt /\
    NameSanitize.sanitize_PAst (NameSanitize.get_sanitizer c1) p = Ok ps /\
    NameSanitize.sanitize_config (NameSanitize.get_sanitizer c1) c1 = Ok c' /\
    exists hw, apply_transforms c' lbox ps (needs_typed c') hw = Ok p'.
Proof.
  unfold peregrine_middle_end, peregrine_front.
  destruct (get_config c attrs) as [c0|e]; cbn -[check_wf_proof with_eq]; [|discriminate].
  set (c1 := if io.(inline_standard) || io.(inline_small) then _ else _).
  destruct (check_wf_proof p) as [hw|] eqn:Hw; cbn -[check_wf_proof with_eq]; [|discriminate].
  destruct (with_eq (NameSanitize.check_sanitized_injective _ _)) as [[[]|] Hi]; cbn -[check_wf_proof with_eq]; [|discriminate].
  destruct (with_eq (NameSanitize.sanitize_PAst _ p)) as [[ps|] Hs]; cbn -[check_wf_proof with_eq]; [|discriminate].
  destruct NameSanitize.sanitize_config as [c2|] eqn:Hc; cbn -[check_wf_proof with_eq]; [|discriminate].
  destruct apply_transforms as [p2|] eqn:Ha; cbn -[check_wf_proof with_eq]; [|discriminate].
  intros [= <- <-]. exists c1, ps.
  split; [|split; [exact (check_wf_proof_ok p hw Hw)|]].
  2: { repeat split; try assumption. eexists. exact Ha. }
  unfold NameSanitize.get_sanitizer. now rewrite (sanitize_config_backend _ _ _ Hc).
Qed.

(** ** Generic lemmas *)

Lemma fo_sat_le (ar ar' : inductive -> nat -> nat) v :
  (forall ind c, ar' ind c <= ar ind c) -> fo_sat ar v -> fo_sat ar' v.
Proof.
  intros Har Hs. induction Hs using fo_sat_ind'.
  { constructor. } { now constructor. }
  constructor. { etransitivity; [apply Har|exact H]. } exact H1.
Qed.

(** Saturation is preserved by an injective renaming, on well-formed values. *)
Lemma fo_sat_rename {efl : EEnvFlags} (hast : has_tApp) rk rn rs Σ v :
  injective_on rk (map fst Σ) ->
  @EWellformed.wellformed efl Σ 0 v -> fo_sat (fo_arity Σ) v ->
  fo_sat (fo_arity (rename_env rk rn rs Σ)) (rename rk rn v).
Proof.
  intros hinj Hwf Hs. revert Hwf.
  induction Hs using fo_sat_ind'; intros Hwf.
  { constructor. } { cbn. rewrite fo_prim_map //. now constructor. }
  rewrite rename_mkApps. cbn.
  rewrite (@EWellformed.wellformed_mkApps efl Σ 0 _ args hast) in Hwf. move/andP: Hwf => [Hc Ha]. cbn in Hc.
  move/andP: Hc => [/andP [_ Hl] _].
  constructor.
  { rewrite length_map. etransitivity; [|exact H].
    unfold fo_arity at 2. unfold fo_arity.
    destruct (lookup_constructor_pars_args Σ ind c) as [[np na]|] eqn:E.
    { rewrite (lookup_constructor_pars_args_rename _ _ _ _ hinj _ _ _ _ E). reflexivity. }
    exfalso. move: E Hl. rewrite /lookup_constructor_pars_args. destruct lookup_constructor as [[[]]|] => //. }
  clear -H1 Ha. induction H1 as [|x l Hx Hl IH]; cbn; constructor; cbn in Ha; move/andP: Ha => [Hx' Hl'].
  { now apply Hx. } now apply IH.
Qed.

(** Dropping constant bodies ([PipelineWf.drop_env_rel]) keeps the arities of
    constructors. *)
Lemma fo_arity_drop Σ' Σ (hrel : drop_env_rel Σ' Σ) ind c : fo_arity Σ' ind c = fo_arity Σ ind c.
Proof. now rewrite /fo_arity (lookup_constructor_pars_args_drop _ _ hrel). Qed.

(** ** The steps of the middle-end *)

(** The remapped constants of a configuration, as in [drop_remapped_bodies]. *)
Definition remapped (c : config) (kn : kername) : bool :=
  List.existsb (fun '(kn', _) => Kernames.eq_kername kn kn') c.(const_remappings_opts).

Lemma drop_remapped_bodies_drop_bodies c env :
  drop_remapped_bodies c env = drop_bodies (remapped c) env.
Proof. reflexivity. Qed.

Lemma check_wf_untyped_sound env t :
  check_wf (Untyped env (Some t)) = Ok tt -> wf_eprogram nocofix_env_flags (env, t).
Proof.
  intros H. apply map_error_ok in H. apply check_wf_program_sound. now rewrite H.
Qed.

Lemma check_wf_typed_sound env t :
  check_wf (Typed env (Some t)) = Ok tt ->
  @wf_glob nocofix_env_flags (ExAst.trans_env env) /\
  @EWellformed.wellformed nocofix_env_flags (ExAst.trans_env env) 0 t.
Proof.
  intros H. apply map_error_ok in H. cbn in H.
  destruct (@CheckWfExAst.check_wf_typed_program nocofix_env_flags env) as [[]|] eqn:E1; cbn in H; [|discriminate].
  split.
  { unfold CheckWfExAst.check_wf_typed_program in E1.
    pose proof (check_wf_globP (efl := nocofix_env_flags) (ExAst.trans_env env)) as R.
    rewrite E1 in R. cbn in R. now inversion R. }
  rewrite -wellformed_equiv H. reflexivity.
Qed.

Lemma sanitize_PAst_untyped f env t ps :
  NameSanitize.sanitize_PAst f (Untyped env (Some t)) = Ok ps ->
  exists env1 t1, NameSanitize.sanitize_untyped_env f env = Ok env1 /\
    NameSanitize.sanitize_term f t = Ok t1 /\ ps = Untyped env1 (Some t1).
Proof.
  cbn. destruct NameSanitize.sanitize_untyped_env as [env1|]; cbn; [|discriminate].
  destruct NameSanitize.sanitize_term as [t1|]; cbn; [|discriminate].
  intros [= <-]. now exists env1, t1.
Qed.

Lemma sanitize_PAst_typed f env t ps :
  NameSanitize.sanitize_PAst f (Typed env (Some t)) = Ok ps ->
  exists env1 t1, NameSanitize.sanitize_typed_env f env = Ok env1 /\
    NameSanitize.sanitize_term f t = Ok t1 /\ ps = Typed env1 (Some t1).
Proof.
  cbn. destruct NameSanitize.sanitize_typed_env as [env1|]; cbn; [|discriminate].
  destruct NameSanitize.sanitize_term as [t1|]; cbn; [|discriminate].
  intros [= <-]. now exists env1, t1.
Qed.

(** ** Corollaries: from the input file to the lambda-box program *)

(** Untyped input, untyped backend, without [--untyped-dearg] (with it, the
    program is dearged through the types inferred for it, see
    [apply_transforms]). *)
Theorem peregrine_untyped_fo {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox p0 env t c' p' v :
  let f := NameSanitize.get_sanitizer c' in
  let env_s := rename_env (NameSanitize.sanitized_kername f) (sanitized_name f) (sanitized_ident f) env in
  let v_s := rename (NameSanitize.sanitized_kername f) (sanitized_name f) v in
  let econf := mk_opts c' false (fun _ => None) in
  let m := mk_cstr_reorders c' in
  let unb := econf.(enable_unsafe).(unboxing) in
  p0 = Untyped env (Some t) ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  needs_typed c' = false ->
  c'.(erasure_opts).(untyped_dearg) = false ->
  fo_sat (fo_arity env) v ->
  (remap_on econf = true -> remap_fo econf (fo_unboxed_value m env_s unb v_s)) ->
  eval_eprogram default_wcbv_flags (env, t) v ->
  exists env' t', p' = Untyped env' (Some t') /\
    eval_eprogram final_wcbv_flags (env', t')
      (fo_value_compile m env_s unb c'.(erasure_opts).(implement_box) v_s).
Proof.
  intros f env_s v_s econf m unb -> hs hme hnt hud hsat hremap [ev].
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_untyped_sound in hwf.
  apply sanitize_PAst_untyped in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf -/f in hinj he ht.
  pose proof (sanitize_correct f env t env1 t1 v _ hinj he ht hwf ev) as [_ ev1].
  apply sanitize_untyped_env_spec in he. apply sanitize_term_spec in ht. subst env1 t1.
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  rewrite hud. cbv beta iota.
  destruct (pipeline_pre_error _) as [[env' t']|] eqn:hr; cbn; [|discriminate].
  intros [= <-]. exists env', t'. split; [reflexivity|].
  apply map_error_ok in hr.
  eapply (run_untyped_transforms_wf_fo econf m _ _ _ _ _ _ (env_s, _)); [exact hr| | exact hremap | now constructor].
  cbn. apply (fo_sat_rename (efl := nocofix_env_flags) eq_refl); [| |exact hsat].
  { eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  destruct hwf as [hwg hwt].
  exact (eval_wellformed (efl := nocofix_env_flags) env eq_refl hwg t v hwt ev).
Qed.

(** The common part of the two typed corollaries: the sanitized program with the
    bodies of remapped constants dropped is saturated and evaluates to the renamed
    value. *)
Lemma typed_sanitized_fo f rem env env_s t v :
  let sk := NameSanitize.sanitized_kername f in
  NameSanitize.sanitize_typed_env f env = Ok env_s ->
  injective_on sk (NameSanitize.typed_env_names env) ->
  @wf_glob nocofix_env_flags (ExAst.trans_env env) ->
  @EWellformed.wellformed nocofix_env_flags (ExAst.trans_env env) 0 t ->
  fo_sat (fo_arity (ExAst.trans_env env)) v ->
  eval_typed_eprogram default_wcbv_flags (drop_bodies (fun kn => rem (sk kn)) env, t) v ->
  fo_sat (fo_arity (ExAst.trans_env (drop_bodies rem env_s))) (rename sk (sanitized_name f) v) /\
  eval_typed_eprogram default_wcbv_flags (drop_bodies rem env_s, rename sk (sanitized_name f) t)
    (rename sk (sanitized_name f) v).
Proof.
  intros sk he hinj hwg hwt hsat [ev].
  set (Σd := ExAst.trans_env (drop_bodies (fun kn => rem (sk kn)) env)).
  have hrel : drop_env_rel Σd (ExAst.trans_env env) by apply drop_env_rel_drop_bodies.
  have hinj' : injective_on sk (map fst Σd).
  { rewrite (map_fst_drop _ _ hrel) map_fst_trans_env. exact hinj. }
  rewrite /= (trans_env_drop_sanitize f rem env env_s he). fold sk. fold Σd.
  split.
  { apply (fo_sat_rename (efl := nocofix_env_flags) eq_refl); [exact hinj'| |].
    { have hwg' : @wf_glob nocofix_env_flags Σd by exact (wf_glob_drop (efl := nocofix_env_flags) eq_refl _ _ hrel hwg).
      have hwt' : @EWellformed.wellformed nocofix_env_flags Σd 0 t
        by exact (wellformed_drop _ _ hrel (efl := nocofix_env_flags) eq_refl 0 t hwt).
      exact (eval_wellformed (efl := nocofix_env_flags) Σd eq_refl hwg' t v hwt' ev). }
    eapply fo_sat_le; [|exact hsat]. intros ind c. now rewrite (fo_arity_drop _ _ hrel). }
  constructor. cbn [fst snd]. rewrite (trans_env_drop_sanitize f rem env env_s he) -/sk -/Σd.
  now apply eval_rename.
Qed.

(** Typed input, untyped backend.  The input is evaluated with the bodies of the
    remapped constants dropped (the pipeline drops them: the backend provides
    them); the program handed to the backend evaluates to the value of
    [run_typed_to_untyped_transforms_fo] for the sanitized program. *)
Theorem peregrine_typed_untyped_fo {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox p0 env t c' p' v :
  let f := NameSanitize.get_sanitizer c' in
  let sk := NameSanitize.sanitized_kername f in
  let v_s := rename sk (sanitized_name f) v in
  let econf env_s :=
    eta_econf (mk_opts c' false (remap_masks c' false env_s)) (drop_remapped_bodies c' env_s) in
  let m := mk_cstr_reorders c' in
  let unb := c'.(erasure_opts).(Config.unboxing) in
  let q env_s := (drop_remapped_bodies c' env_s, rename sk (sanitized_name f) t) in
  p0 = Typed env (Some t) ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  needs_typed c' = false ->
  fo_sat (fo_arity (ExAst.trans_env env)) v ->
  (forall env_s, NameSanitize.sanitize_typed_env f env = Ok env_s ->
   remap_on (econf env_s) = true -> forall pf,
   remap_fo (econf env_s)
     (fo_unboxed_value m (typed_dearged_env (econf env_s) m (q env_s) pf) unb
        (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s))) ->
  eval_typed_eprogram default_wcbv_flags (drop_bodies (fun kn => remapped c' (sk kn)) env, t) v ->
  exists env_s env' t',
    NameSanitize.sanitize_typed_env f env = Ok env_s /\
    p' = Untyped env' (Some t') /\
    exists pf,
      eval_eprogram final_wcbv_flags (env', t')
        (fo_value_compile m (typed_dearged_env (econf env_s) m (q env_s) pf) unb
           c'.(erasure_opts).(implement_box)
           (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s)).
Proof.
  intros f sk v_s econf m unb q -> hs hme hnt hsat hremap ev.
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_typed_sound in hwf as [hwg hwt].
  apply sanitize_PAst_typed in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf -/f in hinj he ht.
  apply sanitize_term_spec in ht. subst t1.
  have hinj' : injective_on sk (NameSanitize.typed_env_names env).
  { eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  destruct (typed_sanitized_fo f (remapped c') env env1 t v he hinj' hwg hwt hsat ev) as [hsat1 ev1].
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  destruct (pipeline_pre_error _) as [[env' t']|] eqn:hr; cbn; [|discriminate].
  intros [= <-]. exists env1, env', t'. split; [exact he|]. split; [reflexivity|].
  apply map_error_ok in hr.
  exact (run_typed_to_untyped_transforms_wf_fo (mk_opts c' false (remap_masks c' false env1)) m _ _ _ _ _ _ (q env1) _ _ v_s hr hsat1
           (hremap env1 he) ev1).
Qed.

(** Typed input, typed backend. *)
Theorem peregrine_typed_typed_fo {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox p0 env t c' p' v :
  let f := NameSanitize.get_sanitizer c' in
  let sk := NameSanitize.sanitized_kername f in
  let v_s := rename sk (sanitized_name f) v in
  let econf env_s :=
    eta_econf (mk_opts c' true (remap_masks c' false env_s)) (drop_remapped_bodies c' env_s) in
  let m := mk_cstr_reorders c' in
  let q env_s := (drop_remapped_bodies c' env_s, rename sk (sanitized_name f) t) in
  p0 = Typed env (Some t) ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  needs_typed c' = true ->
  fo_sat (fo_arity (ExAst.trans_env env)) v ->
  eval_typed_eprogram default_wcbv_flags (drop_bodies (fun kn => remapped c' (sk kn)) env, t) v ->
  exists env_s env' t',
    NameSanitize.sanitize_typed_env f env = Ok env_s /\
    p' = Typed env' (Some t') /\
    exists pf,
      eval_typed_eprogram target_wcbv_flags (env', t')
        (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s).
Proof.
  intros f sk v_s econf m q -> hs hme hnt hsat ev.
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_typed_sound in hwf as [hwg hwt].
  apply sanitize_PAst_typed in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf -/f in hinj he ht.
  apply sanitize_term_spec in ht. subst t1.
  have hinj' : injective_on sk (NameSanitize.typed_env_names env).
  { eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  destruct (typed_sanitized_fo f (remapped c') env env1 t v he hinj' hwg hwt hsat ev) as [hsat1 ev1].
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  destruct (pipeline_pre_error _) as [[mr [env' t']]|] eqn:hr; cbn; [|discriminate].
  intros [= <-]. exists env1, env', t'. split; [exact he|]. split; [reflexivity|].
  apply map_error_ok in hr.
  exact (run_typed_transforms_wf_fo (mk_opts c' true (remap_masks c' false env1)) m _ (q env1) _ _ v_s hr hsat1 ev1).
Qed.
