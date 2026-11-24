(** * Peregrine with the Rust backend: correctness up to the printer

    The Rust backend is typed: the middle-end runs the typed transformation
    pipeline and hands a typed environment [Σt] (an [ExAst.global_env]) and a
    main term to [run_backend], which prints [Σt] with
    [RustBackend.extract_rust].  This file composes the first-order results of
    the middle-end with the backend step: if the input program evaluates to a
    saturated first-order value [v], and Peregrine with the Rust backend
    produces [out], then
    - [out] is the output of the printer [RustExtract.print_program] applied to
      [RustBackend.eta_remapped_bodies remaps Σt], for the remappings [remaps]
      of the configuration ([rust_printed]);
    - the main term evaluates in [ExAst.trans_env Σt] to the value of the
      first-order theorems.

    Covered: typed input ([peregrine_typed_rust_input], from
    [peregrine_typed_typed_fo]) and untyped input
    ([peregrine_untyped_rust_input], through the Hindley-Milner inference
    [infer_for_backend], of which only [ExAst.trans_env env0 = env] is used).

    Remapped constants: the input is evaluated with the bodies of the remapped
    constants removed (they are axioms, as in the pipeline, which drops these
    bodies before the typed transformations).

    Not covered by the proofs (trusted):
    - [RustBackend.eta_remapped_bodies], which replaces the body of every
      remapped constant (including the default remapping of [id],
      [RustBackend.default_const_remaps]) by [fun _ .. _ => □]: the printer
      prints remapped constants from their remapping strings, not from their
      bodies.  It is outside the theorems; [eta_remapped_bodies_eval] shows
      that it preserves evaluation when every constant it changes is an axiom
      ([no_remapped_body], a boolean condition on [Σt]), which holds for the
      instances at the end of the file;
    - the printer [RustExtract.print_program] and the Rust compiler;
    - the main term: [PAst_to_ExAst] passes the environment only, so the
      printed program does not contain the main term. *)

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
  EFirstOrderCorrect EFirstOrderTyped NameSanitizeCorrect PipelineWf PipelineFirstOrder.
From Peregrine Require RustBackend EHindleyMilner.
From TypedExtraction Require Import PrettyPrinterMonad Printing RustExtract.

Import MonadNotation.
Set Default Goal Selector "!".

(** ** The backend step *)

(** The remappings with which [extract_rust] prints [Σ]. *)
Definition rust_remaps (c : config) (Σ : ExAst.global_env) : remaps :=
  RustBackend.mk_remaps (c.(const_remappings_opts) ++ RustBackend.default_const_remaps Σ)%list
    c.(ind_remappings_opts).

(** [out] is the printed form of [Σ]: the printer applied to
    [eta_remapped_bodies (rust_remaps c Σ) Σ]. *)
Definition rust_printed (c : config) (Σ : ExAst.global_env) (out : list string) : Prop :=
  exists opts, c.(backend_opts) = Rust opts /\
    exists st,
      finish_print_lines
        (@print_program (RustBackend.eta_remapped_bodies (rust_remaps c Σ) Σ) (rust_remaps c Σ)
           (RustBackend.mk_config opts) (RustBackend.mk_attributes c.(custom_attributes_opts) opts)
           (RustBackend.mk_preamble opts)) = Ok (st, out).

Local Arguments RustBackend.extract_rust : simpl never.

Lemma bind_ok_inv {A B : Type} (m : result' A) (k : A -> result' B) r :
  (x <- m;; k x) = Ok r -> exists a, m = Ok a /\ k a = Ok r.
Proof. destruct m as [a|e]; cbn; [eauto|discriminate]. Qed.

(** Only the Rust backend produces Rust programs. *)
Lemma peregrine_backend_rust c p file warnings out :
  peregrine_backend c p file = Ok (warnings, RustProgram out) ->
  exists opts Σ, c.(backend_opts) = Rust opts /\ PAst_to_ExAst p = Ok Σ /\
    RustBackend.extract_rust c.(const_remappings_opts) c.(ind_remappings_opts)
      c.(custom_attributes_opts) opts file Σ = Ok out.
Proof.
  unfold peregrine_backend. intros h.
  apply bind_ok_inv in h as (_ & _ & h).
  unfold run_backend in h.
  destruct (backend_opts c) as [opts| | | | | | | | | | | |] eqn:hb;
    repeat (apply bind_ok_inv in h as (? & ? & h)); try discriminate.
  exists opts. match goal with e : PAst_to_ExAst p = Ok ?q |- _ => exists q end.
  injection h as _ <-. auto.
Qed.

Lemma extract_rust_printed c opts file Σ out :
  c.(backend_opts) = Rust opts ->
  RustBackend.extract_rust c.(const_remappings_opts) c.(ind_remappings_opts)
    c.(custom_attributes_opts) opts file Σ = Ok out ->
  rust_printed c Σ out.
Proof.
  intros hb h. exists opts. split; [exact hb|]. revert h.
  unfold RustBackend.extract_rust, rust_remaps. cbv zeta.
  destruct (finish_print_lines _) as [[st s]|e]; intros h; [|discriminate h].
  injection h as <-. now exists st.
Qed.

(** The Rust backend needs typed input. *)
Lemma peregrine_backend_rust_typed c p file warnings out :
  peregrine_backend c p file = Ok (warnings, RustProgram out) -> needs_typed c = true.
Proof.
  intros h. apply peregrine_backend_rust in h as (opts & _ & hb & _).
  unfold needs_typed. now rewrite hb.
Qed.

(** ** [eta_remapped_bodies] and evaluation

    Evaluation in an environment in which some constants are axioms carries
    over to the environment in which they have bodies ([eval_undrop]).  Hence
    when every constant that [eta_remapped_bodies] changes is an axiom, the
    change preserves evaluation ([eta_remapped_bodies_eval]). *)

Section Undrop.
  Context {wfl : WcbvFlags} (Σ' Σ : global_declarations) (hrel : drop_env_rel Σ' Σ).

  Lemma constructor_isprop_pars_decl_drop ind c :
    constructor_isprop_pars_decl Σ' ind c = constructor_isprop_pars_decl Σ ind c.
  Proof. now rewrite /constructor_isprop_pars_decl (lookup_constructor_drop _ _ hrel). Qed.

  Lemma inductive_isprop_and_pars_drop ind :
    inductive_isprop_and_pars Σ' ind = inductive_isprop_and_pars Σ ind.
  Proof. now rewrite /inductive_isprop_and_pars (lookup_inductive_drop _ _ hrel). Qed.

  Lemma atom_drop t : atom Σ' t = atom Σ t.
  Proof. destruct t as [| | | | | | | |ind c []| | | | | | |]; cbn; try reflexivity. now rewrite (lookup_constructor_drop _ _ hrel). Qed.

  Lemma declared_constant_undrop kn decl body :
    declared_constant Σ' kn decl -> cst_body decl = Some body -> declared_constant Σ kn decl.
  Proof.
    rewrite /declared_constant. pose proof (lookup_env_drop _ _ hrel kn) as h.
    destruct (lookup_env Σ' kn), (lookup_env Σ kn); try contradiction; try discriminate.
    intros [= ->] hb. destruct h as [<-|[cb [-> hd]]]; [reflexivity|]. injection hd as ->. discriminate.
  Qed.

  Lemma eval_undrop t v : eval Σ' t v -> eval Σ t v.
  Proof.
    intros ev. induction ev using eval_rect.
    { eapply eval_box; tea. }
    { eapply eval_beta; tea. }
    { eapply eval_zeta; tea. }
    { eapply eval_iota; tea. now rewrite -constructor_isprop_pars_decl_drop. }
    { eapply eval_iota_block; tea. now rewrite -constructor_isprop_pars_decl_drop. }
    { eapply eval_iota_sing; tea. now rewrite -inductive_isprop_and_pars_drop. }
    { eapply eval_fix; tea. }
    { eapply eval_fix_value; tea. }
    { eapply eval_fix'; tea. }
    { eapply eval_cofix_case; tea. }
    { eapply eval_cofix_proj; tea. }
    { eapply eval_delta; [eapply declared_constant_undrop; tea|tea|tea]. }
    { eapply eval_proj; tea. now rewrite -constructor_isprop_pars_decl_drop. }
    { eapply eval_proj_block; tea. now rewrite -constructor_isprop_pars_decl_drop. }
    { eapply eval_proj_prop; tea. now rewrite -inductive_isprop_and_pars_drop. }
    { eapply eval_construct; tea. now rewrite -(lookup_constructor_drop _ _ hrel). }
    { eapply eval_construct_block; tea; [now rewrite -(lookup_constructor_drop _ _ hrel)|].
      clear -iha. revert iha. induction a; cbn; intros iha; constructor; destruct iha; auto. }
    { eapply eval_app_cong; tea. }
    { econstructor. destruct X; cbn; try constructor.
      { clear -a. revert a. induction ev; cbn; intros a; constructor; destruct a; auto. }
      exact e. }
    { eapply eval_force; tea. }
    { eapply eval_atom. now rewrite -atom_drop. }
  Qed.
End Undrop.

(** [eta_remapped_bodies r] changes only constants without a body. *)
Definition no_remapped_body (r : remaps) (Σ : ExAst.global_env) : bool :=
  forallb (fun '(kn, _, d) =>
    match d with
    | ExAst.ConstantDecl cst => negb (isSome (remap_constant r kn)) || negb (isSome (ExAst.cst_body cst))
    | _ => true
    end) Σ.

Lemma drop_env_rel_eta_remapped r Σ :
  no_remapped_body r Σ = true ->
  drop_env_rel (ExAst.trans_env Σ) (ExAst.trans_env (RustBackend.eta_remapped_bodies r Σ)).
Proof.
  rewrite /no_remapped_body /RustBackend.eta_remapped_bodies /ExAst.trans_env.
  induction Σ as [|[[kn b] d] Σ IH]; cbn [forallb map]; [constructor|].
  move/andP => [hd hΣ]. constructor; [|exact (IH hΣ)].
  destruct d as [[ty body]| |]; cbn; try (split; [reflexivity|left; reflexivity]).
  destruct (remap_constant r kn); cbn in hd |- *; (split; [reflexivity|]); [|left; reflexivity].
  destruct body; [discriminate|]. right. eexists. split; reflexivity.
Qed.

Lemma eta_remapped_bodies_eval {wfl : WcbvFlags} r Σ t v :
  no_remapped_body r Σ = true ->
  eval_typed_eprogram wfl (Σ, t) v ->
  eval_typed_eprogram wfl (RustBackend.eta_remapped_bodies r Σ, t) v.
Proof.
  intros h [ev]. constructor. exact (eval_undrop _ _ (drop_env_rel_eta_remapped r Σ h) t v ev).
Qed.

(** ** Untyped input: dropping bodies on the untyped view *)

(** [drop_bodies] on an untyped environment. *)
Definition drop_untyped_bodies (rem : kername -> bool) (env : global_declarations) : global_declarations :=
  map (fun '(kn, d) =>
    match d with
    | ConstantDecl _ => if rem kn then (kn, ConstantDecl {| cst_body := None |}) else (kn, d)
    | _ => (kn, d)
    end) env.

Lemma drop_untyped_bodies_none env : drop_untyped_bodies (fun _ => false) env = env.
Proof.
  rewrite /drop_untyped_bodies.
  induction env as [|[kn d] env IH]; [reflexivity|]. cbn [map]. rewrite IH. now destruct d.
Qed.

(** An environment without type aliases; [ExAst.trans_env] turns a type alias
    into a constant, which [drop_bodies] keeps. *)
Definition no_type_alias (env0 : ExAst.global_env) : Prop :=
  Forall (fun d => match d.2 with ExAst.TypeAliasDecl _ => False | _ => True end) env0.

Lemma infer_no_type_alias Σ Σ' : EHindleyMilner.infer Σ = Ok Σ' -> no_type_alias Σ'.
Proof.
  unfold EHindleyMilner.infer. destruct (EHindleyMilner.infer_sigs Σ) as [[T1 E1]|e]; cbn; intros H; [|discriminate].
  injection H as <-. apply Forall_map, Forall_forall.
  intros [kn [cb|mib]] _; exact I.
Qed.

Lemma trans_env_drop_bodies rem env0 :
  no_type_alias env0 ->
  ExAst.trans_env (drop_bodies rem env0) = drop_untyped_bodies rem (ExAst.trans_env env0).
Proof.
  rewrite /no_type_alias /drop_bodies /drop_untyped_bodies /ExAst.trans_env.
  induction 1 as [|[[kn b] d] env0 hd _ IH]; [reflexivity|]. cbn [map]. rewrite IH. congr (_ :: _).
  destruct d as [cst| |]; cbn in hd |- *; try reflexivity; try contradiction.
  now destruct (rem kn).
Qed.

Lemma drop_env_rel_drop_untyped rem env :
  drop_env_rel (drop_untyped_bodies rem env) env.
Proof.
  rewrite /drop_untyped_bodies.
  induction env as [|[kn d] env IH]; cbn [map]; constructor; [|exact IH].
  destruct d as [cb|mib]; [destruct (rem kn)|]; cbn; split; try reflexivity.
  all: try (left; reflexivity).
  right. now exists cb.
Qed.

Lemma rename_env_drop_untyped rk rn ri rem env :
  rename_env rk rn ri (drop_untyped_bodies (fun kn => rem (rk kn)) env) =
  drop_untyped_bodies rem (rename_env rk rn ri env).
Proof.
  rewrite /rename_env /drop_untyped_bodies.
  induction env as [|[kn d] env IH]; [reflexivity|]. cbn [map]. rewrite IH. congr (_ :: _).
  destruct d as [cb|mib]; cbn; [|reflexivity].
  now destruct (rem (rk kn)).
Qed.

(** ** End-to-end theorems *)

(** Typed input.  The middle-end hands the typed environment [Σt] and the main
    term [t'] to the backend; [out] is the printed form of [Σt], and [t']
    evaluates in [Σt] (types forgotten) to the value of
    [peregrine_typed_typed_fo]. *)
Theorem peregrine_typed_rust_input {guard : PCUICWfEnvImpl.abstract_guard_impl}
    c attrs ir io lbox p0 env t c' p' file warnings out v :
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
  peregrine_backend c' p' file = Ok (warnings, RustProgram out) ->
  fo_sat (fo_arity (ExAst.trans_env env)) v ->
  eval_typed_eprogram default_wcbv_flags (drop_bodies (fun kn => remapped c' (sk kn)) env, t) v ->
  exists env_s Σt t',
    NameSanitize.sanitize_typed_env f env = Ok env_s /\
    p' = Typed Σt (Some t') /\
    rust_printed c' Σt out /\
    exists pf,
      eval_typed_eprogram target_wcbv_flags (Σt, t')
        (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s).
Proof.
  intros f sk v_s econf m q hp hs hme hb hsat hev.
  have hnt := peregrine_backend_rust_typed _ _ _ _ _ hb.
  destruct (peregrine_typed_typed_fo c attrs ir io lbox p0 env t c' p' v hp hs hme hnt hsat hev)
    as (env_s & Σt & t' & he & -> & pf & hev').
  apply peregrine_backend_rust in hb as (opts & Σ & hbo & hx & hr).
  cbn in hx. injection hx as <-.
  exists env_s, Σt, t'. split; [exact he|]. split; [reflexivity|].
  split; [exact (extract_rust_printed c' opts file Σt out hbo hr)|]. now exists pf.
Qed.

(** Untyped input.  The sanitized environment [env_s] is typed by the
    Hindley-Milner inference to [env0] ([ExAst.trans_env env0 = env_s]); the
    typed pipeline runs on [env0] with the remapped bodies dropped.  [out] is
    the printed form of the resulting [Σt], and the main term [t'] evaluates in
    [Σt] (types forgotten) to the renamed value with the constructor arguments
    removed by dearging dropped, as in [peregrine_typed_typed_fo]. *)
Theorem peregrine_untyped_rust_input {guard : PCUICWfEnvImpl.abstract_guard_impl}
    c attrs ir io lbox p0 env t c' p' file warnings out v :
  let f := NameSanitize.get_sanitizer c' in
  let sk := NameSanitize.sanitized_kername f in
  let env_s := rename_env sk (sanitized_name f) (sanitized_ident f) env in
  let v_s := rename sk (sanitized_name f) v in
  let econf env0 :=
    eta_econf (mk_opts c' true (remap_masks c' true env0)) (drop_remapped_bodies c' env0) in
  let m := mk_cstr_reorders c' in
  let q env0 := (drop_remapped_bodies c' env0, rename sk (sanitized_name f) t) in
  p0 = Untyped env (Some t) ->
  strings_ok p0 = true ->
  peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
  peregrine_backend c' p' file = Ok (warnings, RustProgram out) ->
  fo_sat (fo_arity env) v ->
  eval_eprogram default_wcbv_flags (drop_untyped_bodies (fun kn => remapped c' (sk kn)) env, t) v ->
  exists env0 Σt t',
    ExAst.trans_env env0 = env_s /\
    p' = Typed Σt (Some t') /\
    rust_printed c' Σt out /\
    exists pf,
      eval_typed_eprogram target_wcbv_flags (Σt, t')
        (fo_dearg (typed_dearg_masks (econf env0) m (q env0) pf) v_s).
Proof.
  intros f sk env_s v_s econf m q -> hs hme hb hsat [ev].
  have hnt := peregrine_backend_rust_typed _ _ _ _ _ hb.
  rewrite peregrine_middle_end_string_of_PAst // in hme.
  apply peregrine_middle_end_inv in hme as (c1 & ps & hf & hwf & hinj & hsan & hcfg & hw & hat).
  apply check_wf_untyped_sound in hwf as [hwg hwt].
  apply sanitize_PAst_untyped in hsan as (env1 & t1 & he & ht & ->).
  rewrite -hf -/f in hinj he ht.
  apply sanitize_untyped_env_spec in he. apply sanitize_term_spec in ht. subst env1 t1.
  move: hat. rewrite hnt. unfold apply_transforms. cbv zeta.
  unfold infer_for_backend_eq.
  destruct (with_eq (infer_for_backend _)) as [[env0|e] hi]; cbn; [|discriminate].
  have hi' := map_error_ok _ _ _ hi.
  have he0 := EHindleyMilner.infer_section _ _ hi'.
  have hna := infer_no_type_alias _ _ hi'.
  destruct (pipeline_pre_error _) as [[mr [Σt t']]|] eqn:hr; cbn; [|discriminate].
  intros [= <-].
  apply map_error_ok in hr.
  (* The input of the typed pipeline, on its untyped view. *)
  set (Σd := drop_untyped_bodies (fun kn => remapped c' (sk kn)) env).
  have hrel : drop_env_rel Σd env by apply drop_env_rel_drop_untyped.
  have hinj' : injective_on sk (map fst Σd).
  { rewrite (map_fst_drop _ _ hrel). eapply injective_on_incl; [eapply check_sanitized_injective_spec, hinj|].
    intros x hx. apply in_or_app. now left. }
  have htr : ExAst.trans_env (drop_remapped_bodies c' env0) = rename_env sk (sanitized_name f) (sanitized_ident f) Σd.
  { rewrite drop_remapped_bodies_drop_bodies (trans_env_drop_bodies _ _ hna) he0.
    rewrite /Σd rename_env_drop_untyped. reflexivity. }
  have hwg' : @wf_glob nocofix_env_flags Σd by exact (wf_glob_drop (efl := nocofix_env_flags) eq_refl _ _ hrel hwg).
  have hwt' : @EWellformed.wellformed nocofix_env_flags Σd 0 t
    by exact (wellformed_drop _ _ hrel (efl := nocofix_env_flags) eq_refl 0 t hwt).
  have hsat1 : fo_sat (fo_arity (ExAst.trans_env (q env0).1)) v_s.
  { cbn [fst q]. rewrite htr.
    apply (fo_sat_rename (efl := nocofix_env_flags) eq_refl); [exact hinj'| |].
    { exact (eval_wellformed (efl := nocofix_env_flags) Σd eq_refl hwg' t v hwt' ev). }
    eapply fo_sat_le; [|exact hsat]. intros ind c0. now rewrite (fo_arity_drop _ _ hrel). }
  have ev1 : eval_typed_eprogram default_wcbv_flags (q env0) v_s.
  { constructor. cbn [fst snd q]. rewrite htr. now apply eval_rename. }
  destruct (run_typed_transforms_wf_fo (mk_opts c' true (remap_masks c' true env0)) m _ (q env0) _ _ v_s hr hsat1 ev1)
    as [pf hev'].
  apply peregrine_backend_rust in hb as (opts & Σ & hbo & hx & hx').
  cbn in hx. injection hx as <-.
  exists env0, Σt, t'. split; [exact he0|]. split; [reflexivity|].
  split; [exact (extract_rust_printed c' opts file Σt out hbo hx')|]. exists pf. exact hev'.
Qed.

(** ** Non-vacuity

    [negb true] as untyped and as typed input, with the default Rust
    configuration: every hypothesis of the two theorems holds by computation,
    at the executable instance [Erasure.fake_guard_impl]. *)
Module RustInputExamples.
  Import ListNotations.
  Local Open Scope bs_scope.

  Definition bool_kn : kername := (MPfile ["Ex"], "bool").
  Definition negb_kn : kername := (MPfile ["Ex"], "negb").
  Definition bool_ind : inductive := {| inductive_mind := bool_kn; inductive_ind := 0 |}.

  Definition bool_mib : mutual_inductive_body := {|
    ind_finite := Finite; ind_npars := 0;
    ind_bodies := [{| ind_name := "bool"; ind_propositional := false; ind_kelim := Universes.IntoAny;
                      ind_ctors := [mkConstructor "true" 0; mkConstructor "false" 0];
                      ind_projs := [] |}] |}.

  Definition negb_body : term :=
    tLambda (nNamed "b")
      (tCase (bool_ind, 0) (tRel 0) [([], tConstruct bool_ind 1 []); ([], tConstruct bool_ind 0 [])]).

  Definition env_u : global_declarations :=
    [(negb_kn, ConstantDecl {| cst_body := Some negb_body |}); (bool_kn, InductiveDecl bool_mib)].

  Definition bool_tmib : ExAst.mutual_inductive_body := {|
    ExAst.ind_finite := Finite; ExAst.ind_npars := 0;
    ExAst.ind_bodies := [{| ExAst.ind_name := "bool"; ExAst.ind_propositional := false;
                            ExAst.ind_kelim := Universes.IntoAny; ExAst.ind_type_vars := [];
                            ExAst.ind_ctors := [("true", [], 0); ("false", [], 0)];
                            ExAst.ind_projs := [] |}] |}.

  Definition env_t : ExAst.global_env :=
    [(negb_kn, true, ExAst.ConstantDecl {| ExAst.cst_type := ([], ExAst.TArr (ExAst.TInd bool_ind) (ExAst.TInd bool_ind));
                                          ExAst.cst_body := Some negb_body |});
     (bool_kn, true, ExAst.InductiveDecl bool_tmib)].

  (** [negb true] *)
  Definition main : term := tApp (tConst negb_kn) (tConstruct bool_ind 0 []).
  (** [false] *)
  Definition value : term := tConstruct bool_ind 1 [].

  Definition p_u : PAst := Untyped env_u (Some main).
  Definition p_t : PAst := Typed env_t (Some main).

  Definition conf : string + config' := inr (empty_config' (Rust' empty_rust_config')).
  Definition io : inline_opts :=
    {| inline_standard := false; inline_small := false; inline_size_limit := 12; inline_excluded := [] |}.
  Definition file : string := "negb".

  Definition middle_end (p : PAst) :=
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts (Serialize.string_of_PAst p).

  Definition res_u := Eval vm_compute in middle_end p_u.
  Definition res_t := Eval vm_compute in middle_end p_t.
  Definition c_u := Eval vm_compute in match res_u with Ok cp => cp.1 | Err _ => mk_config (empty_config' (Rust' empty_rust_config')) end.
  Definition q_u := Eval vm_compute in match res_u with Ok cp => cp.2 | Err _ => p_u end.
  Definition c_t := Eval vm_compute in match res_t with Ok cp => cp.1 | Err _ => mk_config (empty_config' (Rust' empty_rust_config')) end.
  Definition q_t := Eval vm_compute in match res_t with Ok cp => cp.2 | Err _ => p_t end.
  Definition out_u := Eval vm_compute in
    match peregrine_backend c_u q_u file with Ok (_, RustProgram s) => s | _ => [] end.
  Definition out_t := Eval vm_compute in
    match peregrine_backend c_t q_t file with Ok (_, RustProgram s) => s | _ => [] end.

  Lemma eval_main : @eval default_wcbv_flags env_u main value.
  Proof.
    eapply eval_beta.
    { eapply eval_delta; [reflexivity|reflexivity|]. apply eval_atom. reflexivity. }
    { apply eval_atom. reflexivity. }
    cbn. eapply eval_iota with (c := 0) (args := []) (pars := 0) (cdecl := mkConstructor "true" 0) (br := ([], tConstruct bool_ind 1 [])); try reflexivity.
    { apply eval_atom. reflexivity. }
    cbn. apply eval_atom. reflexivity.
  Qed.

  Lemma fo_sat_value_u : fo_sat (fo_arity env_u) value.
  Proof. apply (fo_sat_construct _ _ _ []); [vm_compute; constructor|constructor]. Qed.

  Lemma fo_sat_value_t : fo_sat (fo_arity (ExAst.trans_env env_t)) value.
  Proof. apply (fo_sat_construct _ _ _ []); [vm_compute; constructor|constructor]. Qed.

  Lemma untyped_hyps :
    p_u = Untyped env_u (Some main) /\
    strings_ok p_u = true /\
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts
      (Serialize.string_of_PAst p_u) = Ok (c_u, q_u) /\
    peregrine_backend c_u q_u file = Ok ([], RustProgram out_u) /\
    fo_sat (fo_arity env_u) value /\
    eval_eprogram default_wcbv_flags
      (drop_untyped_bodies (fun kn => remapped c_u (NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_u) kn)) env_u,
       main) value.
  Proof.
    split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [exact fo_sat_value_u|].
    have -> : drop_untyped_bodies (fun kn => remapped c_u (NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_u) kn)) env_u = env_u
      by vm_compute; reflexivity.
    constructor. exact eval_main.
  Qed.

  Lemma typed_hyps :
    p_t = Typed env_t (Some main) /\
    strings_ok p_t = true /\
    @peregrine_middle_end_string Erasure.fake_guard_impl conf [] false io no_lbox_opts
      (Serialize.string_of_PAst p_t) = Ok (c_t, q_t) /\
    peregrine_backend c_t q_t file = Ok ([], RustProgram out_t) /\
    fo_sat (fo_arity (ExAst.trans_env env_t)) value /\
    eval_typed_eprogram default_wcbv_flags
      (drop_bodies (fun kn => remapped c_t (NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_t) kn)) env_t,
       main) value.
  Proof.
    split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [exact fo_sat_value_t|].
    constructor. cbn [fst snd].
    have -> : ExAst.trans_env (drop_bodies (fun kn => remapped c_t (NameSanitize.sanitized_kername (NameSanitize.get_sanitizer c_t) kn)) env_t) = env_u
      by vm_compute; reflexivity.
    exact eval_main.
  Qed.

  (** The conclusions for the two programs. *)
  Example untyped_instance :=
    let '(conj h1 (conj h2 (conj h3 (conj h4 (conj h5 h6))))) := untyped_hyps in
    @peregrine_untyped_rust_input Erasure.fake_guard_impl conf [] false io no_lbox_opts p_u env_u main
      c_u q_u file [] out_u value h1 h2 h3 h4 h5 h6.

  Example typed_instance :=
    let '(conj h1 (conj h2 (conj h3 (conj h4 (conj h5 h6))))) := typed_hyps in
    @peregrine_typed_rust_input Erasure.fake_guard_impl conf [] false io no_lbox_opts p_t env_t main
      c_t q_t file [] out_t value h1 h2 h3 h4 h5 h6.

  Lemma out_nonempty : out_u <> [] /\ out_t <> [].
  Proof. split; vm_compute; discriminate. Qed.

  (** For these programs no constant is remapped, so the condition of
      [eta_remapped_bodies_eval] holds and the main term evaluates in the
      environment that the printer gets. *)
  Lemma untyped_instance_printed_env :
    exists Σt t' w, q_u = Typed Σt (Some t') /\ rust_printed c_u Σt out_u /\
      eval_typed_eprogram target_wcbv_flags (RustBackend.eta_remapped_bodies (rust_remaps c_u Σt) Σt, t') w.
  Proof.
    destruct untyped_instance as (env0 & Σt & t' & _ & hq & hp & pf & hev).
    exists Σt, t'. eexists. split; [exact hq|]. split; [exact hp|].
    apply eta_remapped_bodies_eval; [|exact hev].
    unfold q_u in hq. injection hq as hΣ _. subst Σt. vm_compute. reflexivity.
  Qed.

  Lemma typed_instance_printed_env :
    exists Σt t' w, q_t = Typed Σt (Some t') /\ rust_printed c_t Σt out_t /\
      eval_typed_eprogram target_wcbv_flags (RustBackend.eta_remapped_bodies (rust_remaps c_t Σt) Σt, t') w.
  Proof.
    destruct typed_instance as (env_s & Σt & t' & _ & hq & hp & pf & hev).
    exists Σt, t'. eexists. split; [exact hq|]. split; [exact hp|].
    apply eta_remapped_bodies_eval; [|exact hev].
    unfold q_t in hq. injection hq as hΣ _. subst Σt. vm_compute. reflexivity.
  Qed.
End RustInputExamples.
