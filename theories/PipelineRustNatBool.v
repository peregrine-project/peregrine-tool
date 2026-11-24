(** * The Rust backend on a function from [nat] to [bool]: one compilation, all inputs

    [PipelineRust] states the correctness of the Rust backend (up to the
    printer) for the main term of one program.  This file derives from it a
    statement about one compiled function and all its inputs.

    The input is a lambda-box program (typed or untyped) whose environment contains a
    constant [f] and the inductives [nat_ind] and [bool_ind], of the shape of
    [nat] and [bool] ([nat_decl], [bool_decl]); the main term of the compiled
    program is [f 0].  The encodings in lambda-box:
    - [nat_val ind n]: the numeral [S (.. (S O))], with [O] the constructor 0 and
      [S] the constructor 1 of [ind];
    - [bool_val ind b]: the constructor 0 ([true]) or 1 ([false]) of [ind].

    Dearging may remove the argument of [f] and the argument of [S]: the masks
    of the analysis decide it, once, for the whole environment.  The
    compiled main term is [f'] applied to [kept_args keep [x]]: [[x]] if
    the argument of [f] is kept, [[]] otherwise ([keep]); the numeral of [n]
    becomes [nat_val_dearged drop ind n], which is [nat_val ind n] unless the
    argument of [S] is removed ([drop]), in which case [S] has no argument.

    Theorem [rust_nat_bool_correct] (typed input; [rust_nat_bool_correct_untyped]
    for untyped input): if Peregrine with the Rust backend compiles the
    program with main term [f 0] to [out], then [out] is the printed form of a
    typed environment [Σt] ([rust_printed]), and for every [n] and [b], if
    [f n] evaluates to [bool_val b] in the input, then [f'] applied to the
    kept arguments, with the dearged numeral of [n], evaluates to [bool_val b]
    in [Σt] (types forgotten).  [f'], [nat_ind] and [bool_ind] are the
    sanitized names; [keep] and [drop] are fixed by the compilation and do not
    depend on [n].  The type of [f] is not a hypothesis: the statement is
    about the inputs [n] on which [f n] evaluates to a boolean.

    The proof runs the transformation pipeline symbolically: on the main
    terms [f n] the pipeline produces the same environment and the same
    dearging masks for all [n] ([run_nat_app]): the dearging analysis
    depends on the main term only through the number of arguments each
    constant is applied to and two checks, which numerals pass.  The
    first-order theorem of the typed pipeline ([run_typed_transforms_wf_fo])
    for the program with main term [f n] is then about the environment [Σt]
    of the one compilation ([run_nat_bool]).  The proof uses proof
    irrelevance (already an assumption of [peregrine_typed_rust_input]) for
    the freshness proofs that the removal of matches on boxes carries.

    Trusted, as in [PipelineRust]: the printer, [eta_remapped_bodies] (shown
    to preserve evaluation for the example, [even_1_printed_env]), the
    preambles and remappings of [extract_rust], and the Rust compiler. *)

From Stdlib Require Import List Lia ssreflect ssrbool ProofIrrelevance.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.SafeChecker Require PCUICWfEnvImpl.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts CheckWf RecursorInlining AutoInlining
  Pipeline PipelineParse.
From Peregrine Require NameSanitize.
From Peregrine Require Import Utils.
From Peregrine Require Import Serialize SerializeRoundtrip SerializeConfig SerializePAst.
From MetaRocq.Common Require Import Kernames BasicAst Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EGlobalEnv EWellformed EProgram EWcbvEval.
From MetaRocq.Erasure Require EOptimizePropDiscr EEnvMap.
From MetaRocq.Erasure.Typed Require ExAst Optimize OptimizeCorrectness ExtractionCorrectness.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ERenameGlobals Transforms EEtaExpand EFirstOrder EFirstOrderEta
  EFirstOrderCorrect EFirstOrderTyped NameSanitizeCorrect PipelineWf PipelineFirstOrder PipelineRust.

Import MonadNotation.
Import Common.Transform.Transform.
Set Default Goal Selector "!".

(** ** Encodings *)

(** The numeral of [n]: constructor 0 of [ind] is zero, constructor 1 the successor. *)
Fixpoint nat_val (ind : inductive) (n : nat) : term :=
  match n with
  | 0 => tConstruct ind 0 []
  | S n => tApp (tConstruct ind 1 []) (nat_val ind n)
  end.

(** Constructor 0 of [ind] is [true], constructor 1 is [false]. *)
Definition bool_val (ind : inductive) (b : bool) : term :=
  tConstruct ind (if b then 0 else 1) [].

(** The numeral after dearging: with [drop] (the argument of the successor is
    unused in the program and removed) the successor has no argument. *)
Definition nat_val_dearged (drop : bool) (ind : inductive) (n : nat) : term :=
  if drop then
    match n with
    | 0 => tConstruct ind 0 []
    | S _ => tConstruct ind 1 []
    end
  else nat_val ind n.

(** The arguments of a call that dearging keeps: all of them or none. *)
Definition kept_args (keep : bool) (args : list term) : list term :=
  if keep then args else [].

(** [ind] has the shape of [nat]: no parameters, constructor 0 without and
    constructor 1 with one argument. *)
Definition nat_decl (Σ : global_declarations) (ind : inductive) : Prop :=
  lookup_constructor_pars_args Σ ind 0 = Some (0, 0) /\
  lookup_constructor_pars_args Σ ind 1 = Some (0, 1).

(** [ind] has the shape of [bool]: no parameters, constructors 0 and 1 without
    arguments. *)
Definition bool_decl (Σ : global_declarations) (ind : inductive) : Prop :=
  lookup_constructor_pars_args Σ ind 0 = Some (0, 0) /\
  lookup_constructor_pars_args Σ ind 1 = Some (0, 0).

(** ** Terms built from constants and constructors by application *)

Inductive capp : term -> Prop :=
| capp_const kn : capp (tConst kn)
| capp_ctor ind c : capp (tConstruct ind c [])
| capp_app u v : capp u -> capp v -> capp (tApp u v).

Lemma capp_nat_val ind n : capp (nat_val ind n).
Proof. induction n; cbn; repeat constructor; assumption. Qed.

Lemma capp_mkApps t args : capp t -> Forall capp args -> capp (mkApps t args).
Proof.
  induction args as [|a args IH] in t |- *; intros ht ha; cbn; [exact ht|].
  inversion ha; subst. apply IH; [constructor|]; assumption.
Qed.

Lemma remove_match_on_box_capp Σ t : capp t -> EOptimizePropDiscr.remove_match_on_box Σ t = t.
Proof. induction 1; cbn; [reflexivity|reflexivity|]. now rewrite IHcapp1 IHcapp2. Qed.

Lemma valid_cases_capp im t : capp t -> Optimize.valid_cases im t = true.
Proof. induction 1; cbn; try reflexivity. now rewrite IHcapp1 IHcapp2. Qed.

Lemma decompose_app_rec_capp t l :
  capp t -> match (decompose_app_rec t l).1 with tConst _ | tConstruct _ _ _ => True | _ => False end.
Proof. induction 1 as [| |u v hu IHu hv IHv] in l |- *; cbn; [exact I|exact I|]. apply IHu. Qed.

Lemma optimize_capp o t : capp t -> optimize o t = t.
Proof.
  induction 1 as [kn|ind c|u v hu IHu hv IHv]; [reflexivity|reflexivity|].
  cbn [optimize map_subterms_fix EBeta.map_subterms]. rewrite IHu IHv.
  unfold rewrite_node. destruct (lbox_let_fun o); [|reflexivity].
  unfold beta_let, decompose_app.
  pose proof (decompose_app_rec_capp (tApp u v) [] (capp_app _ _ hu hv)) as h.
  destruct (decompose_app_rec (tApp u v) []) as [hd args]. cbn in h.
  destruct hd; try contradiction; reflexivity.
Qed.

Lemma rename_nat_val rk rn ind n :
  rename rk rn (nat_val ind n) = nat_val (rename_inductive rk ind) n.
Proof. induction n; cbn; [reflexivity|]. now rewrite IHn. Qed.

Lemma eta_nat_val Σ ind n Γ : nat_decl Σ ind -> eta Σ Γ 0 (nat_val ind n) = nat_val ind n.
Proof.
  intros [h0 h1]. induction n as [|n IH]; cbn -[lookup_constructor_pars_args].
  { now rewrite h0. }
  now rewrite h1 IH.
Qed.

Lemma min_apps_nat_val ind n acc : min_apps 0 (nat_val ind n) acc = acc.
Proof. induction n in acc |- *; cbn; [reflexivity|]. apply IHn. Qed.

Lemma is_expanded_nat_val im cm ind n :
  #|Optimize.get_ctor_mask im ind 0| = 0 -> #|Optimize.get_ctor_mask im ind 1| = 1 ->
  Optimize.is_expanded_aux im cm 0 (nat_val ind n) = true.
Proof.
  intros h0 h1. induction n as [|n IH]; cbn; [now rewrite h0|]. now rewrite IH h1.
Qed.

(** Dearging the numerals and the call. *)
Definition drop_succ (ms : Optimize.dearg_set) (ind : inductive) : bool :=
  match Optimize.get_ctor_mask (Optimize.ind_masks ms) ind 1 with
  | [true] => true
  | _ => false
  end.

Lemma dearg_nat_val ms ind n :
  #|Optimize.get_ctor_mask (Optimize.ind_masks ms) ind 0| = 0 ->
  #|Optimize.get_ctor_mask (Optimize.ind_masks ms) ind 1| = 1 ->
  OptimizeCorrectness.dearg_term ms (nat_val ind n) = nat_val_dearged (drop_succ ms ind) ind n.
Proof.
  intros h0 h1. unfold OptimizeCorrectness.dearg_term, Optimize.dearg, drop_succ.
  destruct (Optimize.get_ctor_mask (Optimize.ind_masks ms) ind 0) eqn:E0; [|discriminate].
  destruct (Optimize.get_ctor_mask (Optimize.ind_masks ms) ind 1) as [|b [|]] eqn:E1; cbn in h1; try lia.
  induction n as [|n IH].
  { cbn. rewrite E0. now destruct b. }
  cbn [nat_val Optimize.dearg_aux]. rewrite E1.
  destruct b; cbn; [reflexivity|]. now rewrite IH.
Qed.

Lemma dearg_ctor0 ms ind c :
  #|Optimize.get_ctor_mask (Optimize.ind_masks ms) ind c| = 0 ->
  OptimizeCorrectness.dearg_term ms (tConstruct ind c []) = tConstruct ind c [].
Proof.
  intros h. unfold OptimizeCorrectness.dearg_term, Optimize.dearg. cbn.
  destruct (Optimize.get_ctor_mask (Optimize.ind_masks ms) ind c); [reflexivity|discriminate].
Qed.

Definition keep_arg (ms : Optimize.dearg_set) (kn : kername) : bool :=
  match Optimize.get_const_mask (Optimize.const_masks ms) kn with
  | true :: _ => false
  | _ => true
  end.

Lemma dearg_call ms kn x :
  #|Optimize.get_const_mask (Optimize.const_masks ms) kn| <= 1 ->
  OptimizeCorrectness.dearg_term ms (tApp (tConst kn) x) =
  mkApps (tConst kn) (kept_args (keep_arg ms kn) [OptimizeCorrectness.dearg_term ms x]).
Proof.
  intros h. unfold OptimizeCorrectness.dearg_term, Optimize.dearg, keep_arg. cbn [Optimize.dearg_aux].
  rewrite OptimizeCorrectness.dearg_single_masked; [|cbn; lia].
  destruct (Optimize.get_const_mask (Optimize.const_masks ms) kn) as [|[] [|]]; cbn in h |- *;
    try reflexivity; lia.
Qed.

(** ** The typed pipeline, computed

    [run_typed_transforms_wf] composes eta-expansion, the removal of matches
    on boxes, the dearging analysis and dearging, and the lambda-box
    simplifications.  [run_eta_typed_lbox_eq] states its result as these
    functions composed; the proof is by computation. *)

Definition lbox_final (lbox : lbox_opts) (p : ExAst.global_env * term) : ExAst.global_env * term :=
  let p := if lbox_iota lbox then lbox_opts_typed_program iota_opts p else p in
  let p := if lbox_case_id lbox then lbox_opts_typed_program case_id_opts p else p in
  if any_lbox_opts (without_case_id lbox) then lbox_opts_typed_program (without_case_id lbox) p else p.

(** The masks of the dearging analysis on [q] ([None] if a check fails). *)
Definition dearg_masks (cf : ETransform.dearging_config) (q : ExAst.global_env * term) : option Optimize.dearg_set :=
  let P := pad_prop_env q.1 in check_dearging_precond (dearg_config cf P q.2) P q.2.

Definition dearg_stage (cf : ETransform.dearging_config) (q : ExAst.global_env * term) : ExAst.global_env * term :=
  dearg ((dearg_masks cf q, pad_prop_env q.1), q.2).

Lemma run_eta_typed_lbox_eq {guard : PCUICWfEnvImpl.abstract_guard_impl} econf lbox m Σ t pr :
  exists h, run (eta_typed_lbox_transform_pipeline econf lbox) (m, (Σ, t)) pr =
    (m, lbox_final lbox (dearg_stage (dearging_config econf)
          (remove_match_on_box_program_typed nocofix_env_flags (eta_expand_typed_program (Σ, t)) h))).
Proof.
  eexists. cbv beta iota zeta delta [run time compose transform eta_typed_lbox_transform_pipeline
    typed_lbox_transform_pipeline typed_transform_pipeline typed_analysis_pipeline
    eta_expand_typed_transform_mapping dearging_transform_mapping dearging_checks_transform_mapping'
    remove_match_on_box_typed_transform_mapping typed_unguarded_fix_transform
    typed_lbox_opts_transformation dearging_transform remove_match_on_box_typed_transform].
  cbn [fst snd]. unfold lbox_final, dearg_stage, dearg_masks.
  destruct (any_lbox_opts _), (lbox_case_id lbox), (lbox_iota lbox); reflexivity.
Qed.

Lemma typed_dearg_masks_eq {guard : PCUICWfEnvImpl.abstract_guard_impl} econf m Σ t pf :
  exists h, typed_dearg_masks econf m (Σ, t) pf =
    dearg_masks (dearging_config econf)
      (remove_match_on_box_program_typed nocofix_env_flags (eta_expand_typed_program (Σ, t)) h).
Proof.
  eexists. unfold typed_dearg_masks, typed_analysed.
  cbv beta iota zeta delta [run time compose transform typed_analysis_pipeline
    dearging_checks_transform_mapping' remove_match_on_box_typed_transform_mapping
    remove_match_on_box_typed_transform].
  cbn [fst snd]. unfold dearg_masks. reflexivity.
Qed.

(** The environment after the removal of matches on boxes. *)
Definition rmb_env (Σ : ExAst.global_env) (fr : ExAst.fresh_globals (eta_expand_ex_env Σ)) :=
  remove_match_on_box_typed_env (map_of_typed_global_env (eta_expand_ex_env Σ) fr) (eta_expand_ex_env Σ).

Lemma rmb_program_capp Σ t h :
  capp t -> eta (ExAst.trans_env Σ) [] 0 t = t ->
  remove_match_on_box_program_typed nocofix_env_flags (eta_expand_typed_program (Σ, t)) h =
  (rmb_env Σ (pre_remove_match_on_box_typed_fresh _ _ h), t).
Proof.
  intros hc he. unfold remove_match_on_box_program_typed, rmb_env. cbn [fst snd].
  apply f_equal2; [reflexivity|].
  change (eta_expand_typed_program (Σ, t)).2 with (eta (ExAst.trans_env Σ) [] 0 t).
  rewrite he. exact (remove_match_on_box_capp _ _ hc).
Qed.

(** ** The masks do not depend on the numeral *)

(** The call [f n]. *)
Definition nat_call (kn : kername) (ind : inductive) (n : nat) : term :=
  tApp (tConst kn) (nat_val ind n).

Lemma capp_nat_call kn ind n : capp (nat_call kn ind n).
Proof. constructor; [constructor|apply capp_nat_val]. Qed.

Lemma capp_nat_val_dearged drop ind n : capp (nat_val_dearged drop ind n).
Proof. destruct drop; [destruct n|]; cbn; try constructor; apply capp_nat_val. Qed.

Lemma eta_nat_call Σ kn ind n : nat_decl Σ ind -> eta Σ [] 0 (nat_call kn ind n) = nat_call kn ind n.
Proof. intros h. unfold nat_call. cbn [eta]. now rewrite eta_nat_val. Qed.

Lemma compute_masks_valid om tc ti Σ d :
  ExtractionCorrectness.compute_masks om tc ti Σ = ResultMonad.Ok d ->
  Optimize.valid_masks_env (Optimize.ind_masks d) (Optimize.const_masks d) Σ = true.
Proof.
  unfold ExtractionCorrectness.compute_masks, Utils.timed.
  destruct (Optimize.analyze_env om Σ) as [cm im]. cbn.
  destruct (Optimize.is_expanded_env _ _ Σ); cbn; [|discriminate].
  destruct (Optimize.valid_masks_env _ _ Σ) eqn:E; cbn; [|discriminate].
  intros [= <-]. exact E.
Qed.

Lemma check_dearging_precond_masks cf P t ms :
  check_dearging_precond cf P t = Some ms ->
  ExtractionCorrectness.compute_masks (overridden_masks cf) (do_trim_const_masks cf) (do_trim_ctor_masks cf) P =
    ResultMonad.Ok ms /\
  Optimize.is_expanded (Optimize.ind_masks ms) (Optimize.const_masks ms) t = true.
Proof.
  unfold check_dearging_precond. destruct closed_env; [|discriminate].
  destruct ExtractionCorrectness.compute_masks as [d|]; [|discriminate].
  destruct (Optimize.valid_cases _ t) eqn:E1, (Optimize.is_expanded _ _ t) eqn:E2; cbn; try discriminate.
  now intros [= <-].
Qed.

(** Constructor masks of the analysed environment have the length of the
    constructor's parameters and arguments. *)
Lemma compute_masks_ctor_len om tc ti Σ fr ind c np na d :
  ExtractionCorrectness.compute_masks om tc ti (pad_prop_env (rmb_env Σ fr)) = ResultMonad.Ok d ->
  lookup_constructor_pars_args (ExAst.trans_env Σ) ind c = Some (np, na) ->
  #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind c| = np + na.
Proof.
  intros Hd Hl. apply compute_masks_valid in Hd as Hv.
  apply (valid_masks_ctor_mask (Optimize.ind_masks d) (Optimize.const_masks d) Σ ind c np na); [|exact Hl].
  intros kn b mib Hin.
  rewrite -(valid_masks_decl_pad _ _ (kn, b, ExAst.InductiveDecl mib)).
  refine (proj1 (List.forallb_forall _ _) Hv _ _).
  apply (in_map (fun d => (d.1, pad_prop_decl d.2)) _ (kn, b, ExAst.InductiveDecl mib)).
  unfold rmb_env, remove_match_on_box_typed_env.
  apply In_map_on_snd_ind; [reflexivity|]. apply In_map_on_snd_ind; [reflexivity|]. exact Hin.
Qed.

Lemma check_dearging_nat cf P kn ind n :
  (forall om tc ti d, ExtractionCorrectness.compute_masks om tc ti P = ResultMonad.Ok d ->
     #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 0| = 0 /\
     #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 1| = 1) ->
  check_dearging_precond (dearg_config cf P (nat_call kn ind n)) P (nat_call kn ind n) =
  check_dearging_precond (dearg_config cf P (nat_call kn ind 0)) P (nat_call kn ind 0).
Proof.
  intros hlen.
  have -> : dearg_config cf P (nat_call kn ind n) = dearg_config cf P (nat_call kn ind 0).
  { unfold dearg_config, min_apps_env, nat_call. cbn [min_apps]. now rewrite !min_apps_nat_val. }
  unfold check_dearging_precond. destruct closed_env; [|reflexivity].
  destruct ExtractionCorrectness.compute_masks as [d|] eqn:E; [|reflexivity].
  destruct (hlen _ _ _ _ E) as [h0 h1].
  rewrite !valid_cases_capp; try apply capp_nat_call.
  unfold Optimize.is_expanded, nat_call. cbn [Optimize.is_expanded_aux].
  now rewrite !is_expanded_nat_val.
Qed.

(** ** The pipeline on the calls [f n] *)

Definition keep_argM (M : option Optimize.dearg_set) (kn : kername) : bool :=
  match M with Some ms => keep_arg ms kn | None => true end.

Lemma lbox_final_capp lbox E t :
  capp t -> lbox_final lbox (E, t) = ((lbox_final lbox (E, tBox)).1, t).
Proof.
  intros h. unfold lbox_final, lbox_opts_typed_program.
  destruct (lbox_iota lbox), (lbox_case_id lbox), (any_lbox_opts _); cbn [fst snd];
    rewrite ?(optimize_capp _ _ h); reflexivity.
Qed.

Lemma with_check_ok_intro {A P : Type} r (sound : Peregrine.Utils.bool_of_result r = true -> P)
  (k : P -> A) x u :
  r = ResultMonad.Ok u -> (forall p, k p = x) -> with_check r sound k = ResultMonad.Ok x.
Proof. intros -> hk. cbn. now rewrite hk. Qed.

Lemma with_check_ok_res {A P : Type} r (sound : Peregrine.Utils.bool_of_result r = true -> P)
  (k : P -> A) a :
  with_check r sound k = ResultMonad.Ok a -> exists u, r = ResultMonad.Ok u.
Proof. unfold with_check. destruct r as [u|e]; [now exists u|discriminate]. Qed.

(** The result of the pipeline on [f n], from its result on [f 0]: the same
    environment, and the call of [f] with the kept arguments. *)
Lemma run_nat_app {guard : PCUICWfEnvImpl.abstract_guard_impl} econf0 m lbox Σ kn ind hwf0 r0 :
  nat_decl (ExAst.trans_env Σ) ind ->
  run_typed_transforms_wf econf0 m lbox (Σ, nat_call kn ind 0) hwf0 = ResultMonad.Ok r0 ->
  exists fr,
    let cf := dearging_config (eta_econf econf0 Σ) in
    let P := pad_prop_env (rmb_env Σ fr) in
    let M := check_dearging_precond (dearg_config cf P (nat_call kn ind 0)) P (nat_call kn ind 0) in
    let E := (lbox_final lbox (dearg ((M, P), tBox))).1 in
    let T n := mkApps (tConst kn) (kept_args (keep_argM M kn) [fo_dearg M (nat_val ind n)]) in
    (forall om tc ti d, ExtractionCorrectness.compute_masks om tc ti P = ResultMonad.Ok d ->
       #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 0| = 0 /\
       #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 1| = 1) /\
    r0 = (m, (E, T 0)) /\
    forall n hwf, run_typed_transforms_wf econf0 m lbox (Σ, nat_call kn ind n) hwf = ResultMonad.Ok (m, (E, T n)).
Proof.
  intros hnat hr0.
  unfold run_typed_transforms_wf in hr0. cbv zeta in hr0.
  destruct (with_check_ok_res _ _ _ _ hr0) as [u hu].
  apply with_check_ok in hr0 as [pr0 ->].
  destruct (run_eta_typed_lbox_eq (eta_econf econf0 Σ) lbox m Σ (nat_call kn ind 0) pr0) as [h0 hrun0].
  set (fr := pre_remove_match_on_box_typed_fresh _ _ h0).
  exists fr. cbv zeta.
  set (cf := dearging_config (eta_econf econf0 Σ)).
  set (P := pad_prop_env (rmb_env Σ fr)).
  set (M := check_dearging_precond (dearg_config cf P (nat_call kn ind 0)) P (nat_call kn ind 0)).
  have hlen : forall om tc ti d, ExtractionCorrectness.compute_masks om tc ti P = ResultMonad.Ok d ->
       #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 0| = 0 /\
       #|Optimize.get_ctor_mask (Optimize.ind_masks d) ind 1| = 1.
  { intros om tc ti d hd. destruct hnat as [hn0 hn1].
    split; [exact (compute_masks_ctor_len _ _ _ _ _ _ _ _ _ _ hd hn0)|exact (compute_masks_ctor_len _ _ _ _ _ _ _ _ _ _ hd hn1)]. }
  (* The run on [f n], for any proof of its precondition. *)
  have hrun : forall n (pr : pre (eta_typed_lbox_transform_pipeline (eta_econf econf0 Σ) lbox) (m, (Σ, nat_call kn ind n))),
      run (eta_typed_lbox_transform_pipeline (eta_econf econf0 Σ) lbox) (m, (Σ, nat_call kn ind n)) pr =
      (m, ((lbox_final lbox (dearg ((M, P), tBox))).1,
           mkApps (tConst kn) (kept_args (keep_argM M kn) [fo_dearg M (nat_val ind n)]))).
  { intros n pr.
    destruct (run_eta_typed_lbox_eq (eta_econf econf0 Σ) lbox m Σ (nat_call kn ind n) pr) as [h hrun].
    rewrite hrun. rewrite (rmb_program_capp _ _ _ (capp_nat_call kn ind n) (eta_nat_call _ kn ind n hnat)).
    rewrite (proof_irrelevance _ (pre_remove_match_on_box_typed_fresh _ _ h) fr).
    unfold dearg_stage, dearg_masks. cbn [fst snd]. fold P. fold cf.
    rewrite (check_dearging_nat cf P kn ind n hlen). fold M.
    f_equal. unfold dearg. cbn [fst snd].
    destruct M as [ms|] eqn:EM.
    { destruct (check_dearging_precond_masks _ _ _ _ EM) as [hc hexp].
      destruct (hlen _ _ _ _ hc) as [h0' h1'].
      have hk : #|Optimize.get_const_mask (Optimize.const_masks ms) kn| <= 1.
      { move: hexp. unfold Optimize.is_expanded, nat_call. cbn [Optimize.is_expanded_aux].
        move/andP => [_ hk1]. now apply Nat.leb_le in hk1. }
      unfold nat_call. rewrite dearg_call //. cbn [fo_dearg keep_argM].
      rewrite (dearg_nat_val ms ind n h0' h1').
      apply lbox_final_capp, capp_mkApps; [constructor|].
      destruct (keep_arg ms kn); cbn; repeat constructor. apply capp_nat_val_dearged. }
    cbn [fo_dearg keep_argM kept_args mkApps].
    apply lbox_final_capp, capp_nat_call. }
  split; [exact hlen|]. split.
  { exact (hrun 0 pr0). }
  intros n hwf. unfold run_typed_transforms_wf. cbv zeta.
  apply (with_check_ok_intro _ _ _ _ u); [exact hu|].
  intros pr. apply hrun.
Qed.

(** ** Auxiliary lemmas for the main theorem *)

Lemma wellformed_nat_call Σ k kn ind n :
  nat_decl Σ ind ->
  @EWellformed.wellformed nocofix_env_flags Σ k (nat_call kn ind 0) ->
  @EWellformed.wellformed nocofix_env_flags Σ k (nat_call kn ind n).
Proof.
  intros [h0 h1]. unfold nat_call. cbn [EWellformed.wellformed].
  move/andP => [/andP [ha hc] _]. rewrite ha hc /=.
  have hl : forall c p a, lookup_constructor_pars_args Σ ind c = Some (p, a) ->
      @EWellformed.wellformed nocofix_env_flags Σ k (tConstruct ind c []).
  { intros c p a. rewrite /lookup_constructor_pars_args.
    destruct (lookup_constructor Σ ind c) as [[[mdecl idecl] cdecl]|] eqn:E; cbn; [|discriminate].
    intros _. now rewrite E. }
  induction n as [|n IH]; cbn [nat_val]; [exact (hl _ _ _ h0)|].
  apply/andP; split; [apply/andP; split; [reflexivity|exact (hl _ _ _ h1)]|exact IH].
Qed.

Lemma fo_sat_bool_val Σ ind b : bool_decl Σ ind -> fo_sat (fo_arity Σ) (bool_val ind b).
Proof.
  intros [h0 h1]. apply (fo_sat_construct _ _ _ []); [|constructor].
  unfold fo_arity. destruct b; [rewrite h0|rewrite h1]; cbn; reflexivity.
Qed.

Definition drop_succM (M : option Optimize.dearg_set) (ind : inductive) : bool :=
  match M with Some ms => drop_succ ms ind | None => false end.

Lemma rename_nat_call rk rn kn ind n :
  rename rk rn (nat_call kn ind n) = nat_call (rk kn) (rename_inductive rk ind) n.
Proof. unfold nat_call. cbn [rename]. now rewrite rename_nat_val. Qed.

(** The pipeline-level statement: the compilation of [f 0] to [(Σt, t')]
    gives, for every [n], the evaluation of [f'] applied to the kept
    arguments with the dearged numeral of [n]. *)
Lemma run_nat_bool {guard : PCUICWfEnvImpl.abstract_guard_impl} econf0 m lbox Σ kn ind bind hwf0 mr Σt t' :
  nat_decl (ExAst.trans_env Σ) ind ->
  bool_decl (ExAst.trans_env Σ) bind ->
  run_typed_transforms_wf econf0 m lbox (Σ, nat_call kn ind 0) hwf0 = ResultMonad.Ok (mr, (Σt, t')) ->
  exists keep drop,
    t' = mkApps (tConst kn) (kept_args keep [nat_val_dearged drop ind 0]) /\
    forall n b,
      eval_typed_eprogram default_wcbv_flags (Σ, nat_call kn ind n) (bool_val bind b) ->
      eval_typed_eprogram target_wcbv_flags
        (Σt, mkApps (tConst kn) (kept_args keep [nat_val_dearged drop ind n])) (bool_val bind b).
Proof.
  intros hnat hbool hr.
  destruct (run_nat_app _ _ _ _ kn ind hwf0 _ hnat hr) as [fr H].
  cbv zeta in H. destruct H as (hlen & hr0 & hrun).
  set (P := pad_prop_env _) in *.
  set (M := check_dearging_precond _ P _) in *.
  injection hr0 as -> -> ->.
  have hnv : forall n, fo_dearg M (nat_val ind n) = nat_val_dearged (drop_succM M ind) ind n.
  { intros n. destruct M as [ms|] eqn:EM; cbn [fo_dearg drop_succM]; [|reflexivity].
    destruct (check_dearging_precond_masks _ _ _ _ EM) as [hc _].
    destruct (hlen _ _ _ _ hc) as [h0 h1]. now apply dearg_nat_val. }
  exists (keep_argM M kn), (drop_succM M ind).
  split; [now rewrite -hnv|].
  intros n b ev.
  have hwf_n : wf_eprogram nocofix_env_flags (ExAst.trans_env Σ, nat_call kn ind n).
  { destruct hwf0 as [hg ht]. split; [exact hg|]. exact (wellformed_nat_call _ _ _ _ n hnat ht). }
  have hsat := fo_sat_bool_val _ _ b hbool.
  destruct (run_typed_transforms_wf_fo _ _ _ (Σ, nat_call kn ind n) hwf_n _ _ (hrun n hwf_n) hsat ev) as [pf hev'].
  destruct (typed_dearg_masks_eq _ _ _ _ pf) as [h hm].
  rewrite hm (rmb_program_capp _ _ h (capp_nat_call _ _ _) (eta_nat_call _ _ _ _ hnat)) in hev'.
  rewrite (proof_irrelevance _ (pre_remove_match_on_box_typed_fresh _ _ h) fr) in hev'.
  unfold dearg_masks in hev'. cbn [fst snd] in hev'. fold P in hev'.
  rewrite (check_dearging_nat _ P kn ind n hlen) -/M in hev'.
  have hbv : fo_dearg M (bool_val bind b) = bool_val bind b.
  { destruct M as [ms|] eqn:EM; cbn [fo_dearg]; [|reflexivity].
    destruct (check_dearging_precond_masks _ _ _ _ EM) as [hc _].
    destruct hbool as [h0 h1]. unfold bool_val.
    apply dearg_ctor0. destruct b.
    { exact (compute_masks_ctor_len _ _ _ _ _ _ _ _ _ _ hc h0). }
    exact (compute_masks_ctor_len _ _ _ _ _ _ _ _ _ _ hc h1). }
  rewrite hbv in hev'. rewrite -hnv. exact hev'.
Qed.

(** ** The theorems *)

(** Typed input.  The program has main term [f 0]; Peregrine with the Rust
    backend compiles it to [out].  Then [out] is the printed form of [Σt], the
    main term of the compiled program is [f'] applied to the kept arguments,
    and for every [n] and [b]: if [f n] evaluates to [bool_val bool_ind b] in
    the input environment (with the bodies of remapped constants dropped, as
    in [peregrine_typed_rust_input]), then [f'] applied to the kept arguments
    with the dearged numeral of [n] evaluates in [Σt] (types forgotten) to
    [bool_val bool' b].  [f' = tConst (sk f)], [nat' = rename_inductive sk
    nat_ind] and [bool' = rename_inductive sk bool_ind] are the names after
    sanitization; [keep] (whether dearging keeps the argument of [f]) and
    [drop] (whether it removes the argument of the successor) are fixed by
    the compilation. *)
Theorem rust_nat_bool_correct {guard : PCUICWfEnvImpl.abstract_guard_impl}
    c attrs ir io lbox env f nat_ind bool_ind c' p' file warnings out :
  let sk := NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c') in
  let p0 := Typed env (Some (nat_call f nat_ind 0)) in
  nat_decl (ExAst.trans_env env) nat_ind ->
  bool_decl (ExAst.trans_env env) bool_ind ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  peregrine_backend c' p' file = Ok (warnings, RustProgram out) ->
  exists Σt keep drop,
    p' = Typed Σt (Some (mkApps (tConst (sk f))
                           (kept_args keep [nat_val_dearged drop (rename_inductive sk nat_ind) 0]))) /\
    rust_printed c' Σt out /\
    forall n b,
      eval_typed_eprogram default_wcbv_flags
        (drop_bodies (fun kn => remapped c' (sk kn)) env, nat_call f nat_ind n) (bool_val bool_ind b) ->
      eval_typed_eprogram target_wcbv_flags
        (Σt, mkApps (tConst (sk f)) (kept_args keep [nat_val_dearged drop (rename_inductive sk nat_ind) n]))
        (bool_val (rename_inductive sk bool_ind) b).
Proof.
  intros sk p0 hnat hbool hs hme hb.
  have hnt := peregrine_backend_rust_typed _ _ _ _ _ hb.
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_typed_sound in hwf as [hwg hwt].
  apply sanitize_PAst_typed in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf in hinj he ht.
  apply sanitize_term_spec in ht. subst t1.
  set (san := NameSanitize.get_sanitizer c') in *.
  set (sn := sanitized_name san) in *.
  have hinj' : injective_on sk (NameSanitize.typed_env_names env).
  { eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  (* The declarations of [nat_ind] and [bool_ind] in the environment of the pipeline. *)
  set (Σd0 := ExAst.trans_env (drop_bodies (fun kn => remapped c' (sk kn)) env)).
  have hrel : drop_env_rel Σd0 (ExAst.trans_env env) by apply drop_env_rel_drop_bodies.
  have hinjd : injective_on sk (map fst Σd0).
  { rewrite (map_fst_drop _ _ hrel) map_fst_trans_env. exact hinj'. }
  have hdecl : forall ind c0 x, lookup_constructor_pars_args (ExAst.trans_env env) ind c0 = Some x ->
      lookup_constructor_pars_args (ExAst.trans_env (drop_remapped_bodies c' env1)) (rename_inductive sk ind) c0 = Some x.
  { intros ind c0 [np na] h. rewrite drop_remapped_bodies_drop_bodies (trans_env_drop_sanitize san (remapped c') env env1 he).
    eapply lookup_constructor_pars_args_rename; [exact hinjd|].
    rewrite (lookup_constructor_pars_args_drop _ _ hrel). exact h. }
  have hnat' : nat_decl (ExAst.trans_env (drop_remapped_bodies c' env1)) (rename_inductive sk nat_ind).
  { destruct hnat as [h0 h1]. split; apply hdecl; assumption. }
  have hbool' : bool_decl (ExAst.trans_env (drop_remapped_bodies c' env1)) (rename_inductive sk bool_ind).
  { destruct hbool as [h0 h1]. split; apply hdecl; assumption. }
  (* The compilation of [f 0]. *)
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  destruct (pipeline_pre_error _) as [[mr [Σt t']]|] eqn:hr; cbn; [|discriminate].
  intros [= <-]. apply map_error_ok in hr.
  move: (wf_drop_remapped_bodies c' env1 _ hw) hr.
  rewrite rename_nat_call. intros hwf0 hr.
  destruct (run_nat_bool _ _ _ _ _ _ _ hwf0 _ _ _ hnat' hbool' hr) as (keep & drop & -> & hev).
  exists Σt, keep, drop. split; [reflexivity|]. split.
  { apply peregrine_backend_rust in hb as (opts & Σ & hbo & hx & hr').
    cbn in hx. injection hx as <-. exact (extract_rust_printed c' opts file _ out hbo hr'). }
  intros n b ev. apply hev.
  have hwt_n := wellformed_nat_call _ _ _ _ n hnat hwt.
  have hsat := fo_sat_bool_val _ _ b hbool.
  destruct (typed_sanitized_fo san (remapped c') env env1 (nat_call f nat_ind n) (bool_val bool_ind b)
              he hinj' hwg hwt_n hsat ev) as [_ ev1].
  rewrite -/sk -/sn rename_nat_call in ev1. exact ev1.
Qed.

(** Untyped input.  As [rust_nat_bool_correct]; the sanitized environment is
    typed by the Hindley-Milner inference before the typed pipeline, as in
    [peregrine_untyped_rust_input]. *)
Theorem rust_nat_bool_correct_untyped {guard : PCUICWfEnvImpl.abstract_guard_impl}
    c attrs ir io lbox env f nat_ind bool_ind c' p' file warnings out :
  let sk := NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c') in
  let p0 := Untyped env (Some (nat_call f nat_ind 0)) in
  nat_decl env nat_ind ->
  bool_decl env bool_ind ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  peregrine_backend c' p' file = Ok (warnings, RustProgram out) ->
  exists Σt keep drop,
    p' = Typed Σt (Some (mkApps (tConst (sk f))
                           (kept_args keep [nat_val_dearged drop (rename_inductive sk nat_ind) 0]))) /\
    rust_printed c' Σt out /\
    forall n b,
      eval_eprogram default_wcbv_flags
        (drop_untyped_bodies (fun kn => remapped c' (sk kn)) env, nat_call f nat_ind n) (bool_val bool_ind b) ->
      eval_typed_eprogram target_wcbv_flags
        (Σt, mkApps (tConst (sk f)) (kept_args keep [nat_val_dearged drop (rename_inductive sk nat_ind) n]))
        (bool_val (rename_inductive sk bool_ind) b).
Proof.
  intros sk p0 hnat hbool hs hme hb.
  have hnt := peregrine_backend_rust_typed _ _ _ _ _ hb.
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_untyped_sound in hwf as [hwg hwt].
  apply sanitize_PAst_untyped in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf in hinj he ht.
  apply sanitize_untyped_env_spec in he. apply sanitize_term_spec in ht. subst env1 t1.
  set (san := NameSanitize.get_sanitizer c') in *.
  set (sn := sanitized_name san) in *.
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  unfold infer_for_backend_eq.
  destruct (with_eq (infer_for_backend _)) as [[env0|e] hi]; cbn; [|discriminate].
  have hi' := map_error_ok _ _ _ hi.
  have he0 := EHindleyMilner.infer_section _ _ hi'.
  have hna := infer_no_type_alias _ _ hi'.
  destruct (pipeline_pre_error _) as [[mr [Σt t']]|] eqn:hr; cbn; [|discriminate].
  intros [= <-].
  apply map_error_ok in hr.
  set (Σd := drop_untyped_bodies (fun kn => remapped c' (sk kn)) env).
  have hrel : drop_env_rel Σd env by apply drop_env_rel_drop_untyped.
  have hinj' : injective_on sk (map fst Σd).
  { rewrite (map_fst_drop _ _ hrel). eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  have htr : ExAst.trans_env (drop_remapped_bodies c' env0) = rename_env sk sn (sanitized_ident san) Σd.
  { rewrite drop_remapped_bodies_drop_bodies (trans_env_drop_bodies _ _ hna) he0.
    rewrite /Σd rename_env_drop_untyped. reflexivity. }
  have hdecl : forall ind c0 x, lookup_constructor_pars_args env ind c0 = Some x ->
      lookup_constructor_pars_args (ExAst.trans_env (drop_remapped_bodies c' env0)) (rename_inductive sk ind) c0 = Some x.
  { intros ind c0 [np na] h. rewrite htr.
    eapply lookup_constructor_pars_args_rename; [exact hinj'|].
    rewrite (lookup_constructor_pars_args_drop _ _ hrel). exact h. }
  have hnat' : nat_decl (ExAst.trans_env (drop_remapped_bodies c' env0)) (rename_inductive sk nat_ind).
  { destruct hnat as [h0 h1]. split; apply hdecl; assumption. }
  have hbool' : bool_decl (ExAst.trans_env (drop_remapped_bodies c' env0)) (rename_inductive sk bool_ind).
  { destruct hbool as [h0 h1]. split; apply hdecl; assumption. }
  destruct (run_nat_bool _ _ _ (drop_remapped_bodies c' env0) (sk f) (rename_inductive sk nat_ind)
              (rename_inductive sk bool_ind) _ _ _ _ hnat' hbool' hr) as (keep & drop & -> & hev).
  exists Σt, keep, drop. split; [reflexivity|]. split.
  { apply peregrine_backend_rust in hb as (opts & Σ & hbo & hx & hr').
    cbn in hx. injection hx as <-. exact (extract_rust_printed c' opts file _ out hbo hr'). }
  intros n b [ev]. apply hev. constructor. cbn [fst snd]. rewrite htr.
  rewrite -(rename_nat_call sk sn).
  change (bool_val (rename_inductive sk bool_ind) b) with (rename sk sn (bool_val bool_ind b)).
  now apply eval_rename.
Qed.

(** ** Non-vacuity

    [even : nat -> bool], defined by a fixpoint, as typed and as untyped
    input, with the default Rust configuration: every hypothesis of the two
    theorems holds by computation, at the executable instance
    [Erasure.fake_guard_impl].  The evaluation of [even 1] to [false] in the
    input is a derivation ([eval_even_1]); the theorems give the evaluation
    of the compiled [even] on the numeral 1 ([even_1_compiled_typed],
    [even_1_compiled_untyped]), also in the environment that the printer
    gets ([even_1_printed_env]).  Dearging keeps the argument of [even]
    ([even_keep]). *)
Module RustNatBoolExamples.
  Import ListNotations.
  Local Open Scope bs_scope.

  Definition nat_kn : kername := (MPfile ["Ex"], "nat").
  Definition bool_kn : kername := (MPfile ["Ex"], "bool").
  Definition even_kn : kername := (MPfile ["Ex"], "even").
  Definition nat_ind : inductive := {| inductive_mind := nat_kn; inductive_ind := 0 |}.
  Definition bool_ind : inductive := {| inductive_mind := bool_kn; inductive_ind := 0 |}.

  Definition nat_tmib : ExAst.mutual_inductive_body := {|
    ExAst.ind_finite := Finite; ExAst.ind_npars := 0;
    ExAst.ind_bodies := [{| ExAst.ind_name := "nat"; ExAst.ind_propositional := false;
                            ExAst.ind_kelim := Universes.IntoAny; ExAst.ind_type_vars := [];
                            ExAst.ind_ctors := [("O", [], 0); ("S", [(nNamed "n", ExAst.TInd nat_ind)], 1)];
                            ExAst.ind_projs := [] |}] |}.

  Definition bool_tmib : ExAst.mutual_inductive_body := {|
    ExAst.ind_finite := Finite; ExAst.ind_npars := 0;
    ExAst.ind_bodies := [{| ExAst.ind_name := "bool"; ExAst.ind_propositional := false;
                            ExAst.ind_kelim := Universes.IntoAny; ExAst.ind_type_vars := [];
                            ExAst.ind_ctors := [("true", [], 0); ("false", [], 0)];
                            ExAst.ind_projs := [] |}] |}.

  (** [fix even n := match n with 0 => true | S m => match m with 0 => false | S k => even k end end] *)
  Definition even_mfix : mfixpoint term :=
    [{| dname := nNamed "even";
        dbody := tLambda (nNamed "n")
          (tCase (nat_ind, 0) (tRel 0)
             [([], tConstruct bool_ind 0 []);
              ([nNamed "m"], tCase (nat_ind, 0) (tRel 0)
                 [([], tConstruct bool_ind 1 []);
                  ([nNamed "k"], tApp (tRel 3) (tRel 0))])]);
        rarg := 0 |}].

  Definition env_t : ExAst.global_env :=
    [(even_kn, true, ExAst.ConstantDecl
        {| ExAst.cst_type := ([], ExAst.TArr (ExAst.TInd nat_ind) (ExAst.TInd bool_ind));
           ExAst.cst_body := Some (tFix even_mfix 0) |});
     (bool_kn, true, ExAst.InductiveDecl bool_tmib);
     (nat_kn, true, ExAst.InductiveDecl nat_tmib)].

  Definition env_u : global_declarations := ExAst.trans_env env_t.

  Definition p_t : PAst := Typed env_t (Some (nat_call even_kn nat_ind 0)).
  Definition p_u : PAst := Untyped env_u (Some (nat_call even_kn nat_ind 0)).

  Definition conf : string + config' := inr (empty_config' (Rust' empty_rust_config')).
  Definition io : inline_opts :=
    {| inline_standard := false; inline_small := false; inline_size_limit := 12; inline_excluded := [] |}.
  Definition file : string := "even".

  Definition middle_end (p : PAst) :=
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts (Serialize.string_of_PAst p).

  Definition res_t := Eval vm_compute in middle_end p_t.
  Definition res_u := Eval vm_compute in middle_end p_u.
  Definition c_t := Eval vm_compute in
    match res_t with Ok cp => cp.1 | Err _ => mk_config (empty_config' (Rust' empty_rust_config')) end.
  Definition q_t := Eval vm_compute in match res_t with Ok cp => cp.2 | Err _ => p_t end.
  Definition c_u := Eval vm_compute in
    match res_u with Ok cp => cp.1 | Err _ => mk_config (empty_config' (Rust' empty_rust_config')) end.
  Definition q_u := Eval vm_compute in match res_u with Ok cp => cp.2 | Err _ => p_u end.
  Definition out_t := Eval vm_compute in
    match peregrine_backend c_t q_t file with Ok (_, RustProgram s) => s | _ => [] end.
  Definition out_u := Eval vm_compute in
    match peregrine_backend c_u q_u file with Ok (_, RustProgram s) => s | _ => [] end.

  Definition sk_t := NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_t).
  Definition sk_u := NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_u).

  Lemma typed_decls : nat_decl (ExAst.trans_env env_t) nat_ind /\ bool_decl (ExAst.trans_env env_t) bool_ind.
  Proof. split; split; reflexivity. Qed.
  Lemma typed_strings : strings_ok (Typed env_t (Some (nat_call even_kn nat_ind 0))) = true.
  Proof. vm_compute; reflexivity. Qed.
  Lemma typed_middle_end :
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts
      (Serialize.string_of_PAst (Typed env_t (Some (nat_call even_kn nat_ind 0)))) = Ok (c_t, q_t).
  Proof. vm_compute; reflexivity. Qed.
  Lemma typed_backend : peregrine_backend c_t q_t file = Ok ([], RustProgram out_t).
  Proof. vm_compute; reflexivity. Qed.

  Lemma untyped_decls : nat_decl env_u nat_ind /\ bool_decl env_u bool_ind.
  Proof. split; split; reflexivity. Qed.
  Lemma untyped_strings : strings_ok (Untyped env_u (Some (nat_call even_kn nat_ind 0))) = true.
  Proof. vm_compute; reflexivity. Qed.
  Lemma untyped_middle_end :
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts
      (Serialize.string_of_PAst (Untyped env_u (Some (nat_call even_kn nat_ind 0)))) = Ok (c_u, q_u).
  Proof. vm_compute; reflexivity. Qed.
  Lemma untyped_backend : peregrine_backend c_u q_u file = Ok ([], RustProgram out_u).
  Proof. vm_compute; reflexivity. Qed.

  Example typed_instance :=
    @rust_nat_bool_correct Erasure.fake_guard_impl conf [] false io no_lbox_opts env_t even_kn nat_ind bool_ind
      c_t q_t file [] out_t (proj1 typed_decls) (proj2 typed_decls) typed_strings typed_middle_end typed_backend.

  Example untyped_instance :=
    @rust_nat_bool_correct_untyped Erasure.fake_guard_impl conf [] false io no_lbox_opts env_u even_kn nat_ind
      bool_ind c_u q_u file [] out_u (proj1 untyped_decls) (proj2 untyped_decls) untyped_strings
      untyped_middle_end untyped_backend.

  Lemma out_nonempty : out_t <> [] /\ out_u <> [].
  Proof. split; vm_compute; discriminate. Qed.

  (** [even 1] evaluates to [false] in the input. *)
  Lemma eval_even_1 :
    @eval default_wcbv_flags env_u (nat_call even_kn nat_ind 1) (bool_val bool_ind false).
  Proof.
    unfold nat_call, bool_val. cbn [nat_val].
    have ev1 : @eval default_wcbv_flags env_u
        (tApp (tConstruct nat_ind 1 []) (tConstruct nat_ind 0 []))
        (tApp (tConstruct nat_ind 1 []) (tConstruct nat_ind 0 [])).
    { eapply eval_construct with (ind := nat_ind) (c := 1) (args := []); [reflexivity|reflexivity| |cbn; auto|].
      { apply eval_atom. reflexivity. }
      apply eval_atom. reflexivity. }
    eapply eval_fix with (argsv := []) (mfix := even_mfix) (idx := 0); [reflexivity| |exact ev1|reflexivity|].
    { eapply eval_delta; [reflexivity|reflexivity|]. apply eval_atom. reflexivity. }
    cbn. eapply eval_beta; [apply eval_atom; reflexivity|exact ev1|].
    cbn. eapply eval_iota with (c := 1) (args := [tConstruct nat_ind 0 []]);
      [reflexivity|exact ev1|reflexivity|reflexivity|reflexivity|reflexivity|].
    cbn. eapply eval_iota with (c := 0) (args := []);
      [reflexivity|apply eval_atom; reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
    cbn. apply eval_atom. reflexivity.
  Qed.

  (** The compiled [even] applied to the dearged numeral 1 evaluates to [false]. *)
  Lemma even_1_compiled_typed :
    exists Σt keep drop,
      q_t = Typed Σt (Some (mkApps (tConst (sk_t even_kn))
                              (kept_args keep [nat_val_dearged drop (rename_inductive sk_t nat_ind) 0]))) /\
      rust_printed c_t Σt out_t /\
      eval_typed_eprogram target_wcbv_flags
        (Σt, mkApps (tConst (sk_t even_kn)) (kept_args keep [nat_val_dearged drop (rename_inductive sk_t nat_ind) 1]))
        (bool_val (rename_inductive sk_t bool_ind) false).
  Proof.
    destruct typed_instance as (Σt & keep & drop & hq & hp & hev).
    exists Σt, keep, drop. split; [exact hq|]. split; [exact hp|].
    apply hev. constructor. cbn [fst snd].
    have -> : ExAst.trans_env (drop_bodies (fun kn => remapped c_t (sk_t kn)) env_t) = env_u
      by vm_compute; reflexivity.
    exact eval_even_1.
  Qed.

  Lemma even_1_compiled_untyped :
    exists Σt keep drop,
      q_u = Typed Σt (Some (mkApps (tConst (sk_u even_kn))
                              (kept_args keep [nat_val_dearged drop (rename_inductive sk_u nat_ind) 0]))) /\
      rust_printed c_u Σt out_u /\
      eval_typed_eprogram target_wcbv_flags
        (Σt, mkApps (tConst (sk_u even_kn)) (kept_args keep [nat_val_dearged drop (rename_inductive sk_u nat_ind) 1]))
        (bool_val (rename_inductive sk_u bool_ind) false).
  Proof.
    destruct untyped_instance as (Σt & keep & drop & hq & hp & hev).
    exists Σt, keep, drop. split; [exact hq|]. split; [exact hp|].
    apply hev. constructor. cbn [fst snd].
    have -> : drop_untyped_bodies (fun kn => remapped c_u (sk_u kn)) env_u = env_u
      by vm_compute; reflexivity.
    exact eval_even_1.
  Qed.

  (** Dearging keeps the argument of [even]: the compiled main term is
      [even'] applied to the numeral 0. *)
  Lemma even_keep Σt keep drop :
    q_t = Typed Σt (Some (mkApps (tConst (sk_t even_kn))
                            (kept_args keep [nat_val_dearged drop (rename_inductive sk_t nat_ind) 0]))) ->
    keep = true.
  Proof. destruct keep; [reflexivity|]. vm_compute. intros h. discriminate h. Qed.

  (** No constant of the compiled environment is remapped, so the condition
      of [eta_remapped_bodies_eval] holds and the evaluation carries over to
      the environment that the printer gets. *)
  Lemma even_1_printed_env :
    exists Σt keep drop,
      q_t = Typed Σt (Some (mkApps (tConst (sk_t even_kn))
                              (kept_args keep [nat_val_dearged drop (rename_inductive sk_t nat_ind) 0]))) /\
      rust_printed c_t Σt out_t /\
      eval_typed_eprogram target_wcbv_flags
        (RustBackend.eta_remapped_bodies (rust_remaps c_t Σt) Σt,
         mkApps (tConst (sk_t even_kn)) (kept_args keep [nat_val_dearged drop (rename_inductive sk_t nat_ind) 1]))
        (bool_val (rename_inductive sk_t bool_ind) false).
  Proof.
    destruct even_1_compiled_typed as (Σt & keep & drop & hq & hp & hev).
    exists Σt, keep, drop. split; [exact hq|]. split; [exact hp|].
    apply eta_remapped_bodies_eval; [|exact hev].
    move: hq. unfold q_t. intros [= hΣ _]. subst Σt. vm_compute. reflexivity.
  Qed.
End RustNatBoolExamples.
