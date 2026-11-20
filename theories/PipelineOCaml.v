(** * End-to-end correctness of Peregrine with the OCaml backend

    This file composes the first-order results of the middle-end
    ([PipelineFirstOrder]) with the correctness theorem of verified
    extraction's compilation to Malfunction
    ([Malfunction.CompileCorrect.compile_correct]).

    The [Transform.t] record [OCamlBackend.malfunction_pipeline] (name
    annotation followed by [compile_to_malfunction]) has the trivial target
    relation [fun _ _ => True], so it says nothing about the evaluation of the
    Malfunction program.  Here the semantic content is taken from
    [compile_correct] directly:
    - [name_annotation] (a [Transform.t] with a non-trivial target relation)
      turns the evaluation of the lambda-box program into the evaluation
      [EWcbvEvalNamed.eval] of the annotated program to a named value [vn]
      that represents the lambda-box value;
    - [compile_correct], applied to the annotated program, gives the
      evaluation of the compiled main term in Malfunction's big-step semantics
      [Malfunction.SemanticsSpec.eval] to [Malfunction.CompileCorrect.compile_value Σn vn].

    The OCaml backend compiles the program in which every axiom (an axiom of
    the input or a remapped constant whose body the middle-end drops) has the
    placeholder body [fun x => x] ([ExtractionCheck.fill_axioms]); it checks
    the preconditions of the verified passes on that program
    ([OCamlBackend.malfunction_check]) and warns when they fail.  Evaluation
    in the program with axioms carries over to the filled program
    ([eval_fill_axioms]), since a successful evaluation does not unfold a
    constant without a body.

    As in [compile_correct], the values of the global definitions of the
    Malfunction program are a parameter [Σ'] of the semantics, constrained by
    [Malfunction.CompileCorrect.malfunction_env_prop]: every constant whose body
    evaluates to a named value [w] is bound in [Σ'] to
    [compile_value Σn w].  For the placeholders of axioms, this is the
    compiled identity function; [ExtractionCheck.restore_axioms] replaces
    their compiled bodies in the printed output by the external realization,
    whose agreement with the placeholder is not covered.

    Not covered by the proofs (trusted): the printing of the Malfunction AST
    ([OCamlBackend.print_program]), the [malfunction] tool and the OCaml
    compiler, the agreement of [SemanticsSpec] with them, and remapped
    constants. *)

From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.SafeChecker Require PCUICWfEnvImpl.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts CheckWf RecursorInlining AutoInlining
  Pipeline PipelineParse.
From Peregrine Require NameSanitize.
From Peregrine Require Import Utils.
From Peregrine Require Import Serialize SerializeRoundtrip SerializeConfig SerializePAst.
From MetaRocq.Common Require Import Kernames BasicAst Transform.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EGlobalEnv EWellformed EProgram EWcbvEval.
From MetaRocq.Erasure Require EWcbvEvalNamed.
From MetaRocq.Erasure.Typed Require ExAst.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ERenameGlobals Transforms EFirstOrder EFirstOrderEta
  EFirstOrderCorrect EFirstOrderTyped NameSanitizeCorrect PipelineWf PipelineFirstOrder.
From Peregrine Require ExtractionCheck OCamlBackend.
From Malfunction Require SemanticsSpec CompileCorrect.
From Malfunction Require PipelineCorrect.

Import MonadNotation.
Import Transform.Transform.

(** ** Evaluation in the program with filled axioms *)

Section Undrop.
  Context (Σ' Σ : global_declarations) (hrel : drop_env_rel Σ' Σ).

  Lemma constructor_isprop_pars_decl_drop ind c :
    constructor_isprop_pars_decl Σ' ind c = constructor_isprop_pars_decl Σ ind c.
  Proof. now rewrite /constructor_isprop_pars_decl (lookup_constructor_drop _ _ hrel). Qed.

  Lemma inductive_isprop_and_pars_drop ind :
    inductive_isprop_and_pars Σ' ind = inductive_isprop_and_pars Σ ind.
  Proof. now rewrite /inductive_isprop_and_pars (lookup_inductive_drop _ _ hrel). Qed.

  Lemma atom_drop {wfl : WcbvFlags} t : atom Σ' t = atom Σ t.
  Proof.
    destruct t => //=.
    match goal with |- context [match ?a with [] => _ | _ :: _ => _ end] => destruct a end => //.
    now rewrite (lookup_constructor_drop _ _ hrel).
  Qed.

  Lemma declared_constant_undrop c decl body :
    declared_constant Σ' c decl -> cst_body decl = Some body -> declared_constant Σ c decl.
  Proof.
    rewrite /declared_constant. intros hd hb. pose proof (lookup_env_drop _ _ hrel c) as h.
    rewrite hd in h. destruct (lookup_env Σ c) as [d|] => //.
    destruct h as [<-|[cb [-> [= e]]]]; [reflexivity|]. now subst decl.
  Qed.

  Local Ltac fin :=
    rewrite -?constructor_isprop_pars_decl_drop -?inductive_isprop_and_pars_drop
      -?(lookup_constructor_drop _ _ hrel) -?atom_drop; tea.

  (** Evaluation in an environment with dropped bodies is evaluation in the
      environment with the bodies. *)
  Lemma eval_undrop {wfl : WcbvFlags} t v : eval Σ' t v -> eval Σ t v.
  Proof.
    intros ev.
    induction ev using eval_rect.
    - eapply eval_box; fin.
    - eapply eval_beta; fin.
    - eapply eval_zeta; fin.
    - eapply eval_iota; fin.
    - eapply eval_iota_block; fin.
    - eapply eval_iota_sing; fin.
    - eapply eval_fix; fin.
    - eapply eval_fix_value; fin.
    - eapply eval_fix'; fin.
    - eapply eval_cofix_case; fin.
    - eapply eval_cofix_proj; fin.
    - eapply eval_delta; [|eassumption|exact IHev]. now eapply declared_constant_undrop.
    - eapply eval_proj; fin.
    - eapply eval_proj_block; fin.
    - eapply eval_proj_prop; fin.
    - eapply eval_construct; fin.
    - eapply eval_construct_block; fin.
      clear -iha. revert iha. induction a; cbn; intros iha; constructor; destruct iha; auto.
    - eapply eval_app_cong; fin.
    - econstructor.
      destruct X; cbn; try constructor.
      + cbn. clear -a. revert a. induction ev; cbn; intros a; constructor; destruct a; auto.
      + exact e.
    - eapply eval_force; fin.
    - eapply eval_atom; fin.
  Qed.
End Undrop.

Lemma drop_env_rel_fill_axioms Σ : drop_env_rel Σ (ExtractionCheck.fill_axioms Σ).
Proof.
  induction Σ as [|[kn d] Σ IH]; cbn; constructor; [|exact IH].
  destruct (ExtractionCheck.is_axiom (kn, d)) eqn:ha; cbn; split; try reflexivity.
  - right. destruct d as [[[]]|] => //. now eexists.
  - now left.
Qed.

Lemma eval_fill_axioms {wfl : WcbvFlags} Σ t v :
  eval Σ t v -> eval (ExtractionCheck.fill_axioms Σ) t v.
Proof. apply eval_undrop, drop_env_rel_fill_axioms. Qed.

(** ** Correctness of the compilation to Malfunction *)

Section OCamlCorrect.
  Context `{HP : Malfunction.SemanticsSpec.Pointer} `{HH : @Malfunction.SemanticsSpec.Heap HP}.

  (** The named environment that [OCamlBackend.compile_ocaml] compiles. *)
  Definition annotated_env (p : EAst.program) :=
    EWcbvEvalNamed.annotate_env [] p.1.

  (** If [p] passes [malfunction_check] and evaluates to [v], then [v] is
      represented by a named value [vn], and for every value environment [Σ']
      of the global definitions in the sense of
      [Malfunction.CompileCorrect.malfunction_env_prop], the main term of the compiled
      program evaluates in [Malfunction.SemanticsSpec.eval] to [compile_value Σn vn],
      leaving every heap unchanged. *)
  Lemma ocaml_pipeline_correct p v :
    bool_of_result (OCamlBackend.malfunction_check p) = true ->
    eval_eprogram final_wcbv_flags p v ->
    exists vn, ∥ EWcbvEvalNamed.represents_value vn v ∥ /\
      forall Σ', Malfunction.CompileCorrect.malfunction_env_prop (annotated_env p) Σ' ->
      forall h, Malfunction.SemanticsSpec.eval Σ' Malfunction.SemanticsSpec.empty_locals h (OCamlBackend.compile_ocaml p).2
                  h (Malfunction.CompileCorrect.compile_value (annotated_env p) vn).
  Proof.
    intros hc hev.
    pose proof (OCamlBackend.malfunction_check_sound p hc) as pr.
    destruct (preservation Malfunction.Pipeline.name_annotation p v pr hev) as (vn & [hevn] & hobs).
    pose proof (correctness Malfunction.Pipeline.name_annotation p pr) as [hg _].
    exists vn. split; [exact hobs|].
    intros Σ' hΣ' h.
    eapply Malfunction.CompileCorrect.compile_correct with (Γ := []).
    - intros i mb ob hl. split.
      + exact (Malfunction.Pipeline.few_enough_constructors _ _ hg i mb ob hl).
      + exact (Malfunction.Pipeline.few_enough_arguments_in_constructors _ _ hg i mb ob hl).
    - intros na. reflexivity.
    - exact hΣ'.
    - exact (Malfunction.Pipeline.good_for_extraction_supported_env _ hg).
    - reflexivity.
    - exact (Malfunction.Pipeline.good_for_extraction_supported_term _ hg).
    - exact hevn.
  Qed.

  (** Constructor trees: first-order values without boxes and primitives. *)
  Fixpoint fo_cstrb (t : EAst.term) : bool :=
    match t with
    | EAst.tConstruct _ _ args => forallb fo_cstrb args
    | _ => false
    end.

  (** On constructor trees, the named value is [Malfunction.PipelineCorrect.eval_fo]. *)
  Lemma represents_value_fo_cstr v vn :
    fo_cstrb v = true -> EWcbvEvalNamed.represents_value vn v ->
    vn = Malfunction.PipelineCorrect.eval_fo v.
  Proof.
    induction v in vn |- * using EInduction.term_forall_list_ind; cbn; try discriminate.
    intros hf hr. inversion hr; subst.
    match goal with H : EPrimitive.All2_Set _ _ _ |- _ => rename H into hvs end.
    f_equal. clear hr. induction hvs as [|vn' t' vs' ts' hr' hvs' IH] in X, hf |- *; cbn in *; [reflexivity|].
    apply andb_true_iff in hf as [hf1 hf2].
    inversion X as [|? ? hP hX]; subst.
    now rewrite (hP _ hf1 hr') (IH hX hf2).
  Qed.

  Corollary ocaml_pipeline_correct_fo p v :
    bool_of_result (OCamlBackend.malfunction_check p) = true ->
    eval_eprogram final_wcbv_flags p v ->
    fo_cstrb v = true ->
    forall Σ', Malfunction.CompileCorrect.malfunction_env_prop (annotated_env p) Σ' ->
    forall h, Malfunction.SemanticsSpec.eval Σ' Malfunction.SemanticsSpec.empty_locals h (OCamlBackend.compile_ocaml p).2
                h (Malfunction.CompileCorrect.compile_value (annotated_env p) (Malfunction.PipelineCorrect.eval_fo v)).
  Proof.
    intros hc hev hfo Σ' hΣ' h.
    destruct (ocaml_pipeline_correct p v hc hev) as (vn & [hr] & hm).
    rewrite -(represents_value_fo_cstr v vn hfo hr). exact (hm Σ' hΣ' h).
  Qed.
End OCamlCorrect.

(** ** The OCaml backend in the pipeline *)

Local Arguments OCamlBackend.extract_ocaml : simpl never.

Lemma bind_Ok {A B} (x : A) (f : A -> result' B) : (y <- Ok x;; f y) = f x.
Proof. reflexivity. Qed.

Lemma bind_Err {A B} (e : string) (f : A -> result' B) : (y <- Err e;; f y) = Err e.
Proof. reflexivity. Qed.

(** Only the OCaml backend produces OCaml programs.  The proof avoids
    reducing the other backends, which makes the kernel check slow. *)
Lemma peregrine_backend_ocaml c p file warnings out :
  peregrine_backend c p file = Ok (warnings, OCamlProgram out) ->
  exists opts q, c.(backend_opts) = OCaml opts /\ PAst_to_EAst p = Ok q /\
    OCamlBackend.extract_ocaml c.(const_remappings_opts) c.(custom_attributes_opts) opts file q
      = Ok (warnings, out).
Proof.
  unfold peregrine_backend. intros h.
  destruct (check_lowered c p) as [u|e] eqn:hl; [|discriminate h].
  change (run_backend c file p = Ok (warnings, OCamlProgram out)) in h.
  unfold run_backend in h.
  destruct (backend_opts c) eqn:hb; cbv beta iota zeta in h;
    repeat (match type of h with
            | context [@bind _ _ _ _ ?x _] =>
                let e := fresh "e" in
                destruct x eqn:e; [rewrite bind_Ok in h|rewrite bind_Err in h; discriminate h]
            end);
    try discriminate h.
  match goal with
  | hb : backend_opts c = OCaml ?opts, e : PAst_to_EAst p = Ok ?q,
    e' : OCamlBackend.extract_ocaml _ _ _ _ _ = Ok ?r |- _ =>
      exists opts, q; destruct r; injection h as -> ->; auto
  end.
Qed.

Section OCamlOutput.
  Context `{HP : Malfunction.SemanticsSpec.Pointer} `{HH : @Malfunction.SemanticsSpec.Heap HP}.

  (** The correctness of the OCaml output [out] for the lambda-box program
      [(env, t)] with value [v], for the remappings [rs] and program type [pt]:
      [out] prints the compiled program [m] of [p0], the program with filled
      axioms, with the compiled placeholders dropped again; and [v] is
      represented by a named value [vn] such that, for every value environment
      [Σ'] of the global definitions of [p0], the main term of [m] evaluates
      to [compile_value Σn vn]. *)
  Definition ocaml_output_correct rs pt (env : global_declarations) (t : term)
      (out : list string * string) (v : term) : Prop :=
    let p0 := (ExtractionCheck.fill_axioms env, t) in
    let m := OCamlBackend.compile_ocaml p0 in
    let Σn := annotated_env p0 in
    out = OCamlBackend.print_program (OCamlBackend.mk_remaps rs) pt (OCamlBackend.extract_names t)
            (ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names env) m.1, m.2) /\
    exists vn, ∥ EWcbvEvalNamed.represents_value vn v ∥ /\
      forall Σ', Malfunction.CompileCorrect.malfunction_env_prop Σn Σ' ->
      forall h, Malfunction.SemanticsSpec.eval Σ' Malfunction.SemanticsSpec.empty_locals h m.2 h (Malfunction.CompileCorrect.compile_value Σn vn).

  (** On constructor trees, the Malfunction value is [compile_value] of
      [Malfunction.PipelineCorrect.eval_fo v]. *)
  Lemma ocaml_output_correct_fo rs pt env t out v :
    ocaml_output_correct rs pt env t out v ->
    fo_cstrb v = true ->
    let p0 := (ExtractionCheck.fill_axioms env, t) in
    forall Σ', Malfunction.CompileCorrect.malfunction_env_prop (annotated_env p0) Σ' ->
    forall h, Malfunction.SemanticsSpec.eval Σ' Malfunction.SemanticsSpec.empty_locals h (OCamlBackend.compile_ocaml p0).2
                h (Malfunction.CompileCorrect.compile_value (annotated_env p0) (Malfunction.PipelineCorrect.eval_fo v)).
  Proof.
    intros [_ (vn & [hr] & h)] hfo; cbv zeta; intros Σ' hΣ' hp.
    rewrite -(represents_value_fo_cstr v vn hfo hr). exact (h Σ' hΣ' hp).
  Qed.

  (** The OCaml backend is correct on lambda-box programs for which it reports
      no warning. *)
  Lemma ocaml_backend_correct c env t file warnings out v :
    peregrine_backend c (Untyped env (Some t)) file = Ok (warnings, OCamlProgram out) ->
    warnings = [] ->
    eval_eprogram final_wcbv_flags (env, t) v ->
    exists opts, c.(backend_opts) = OCaml opts /\
      ocaml_output_correct c.(const_remappings_opts) opts.(Config.program_type) env t out v.
  Proof.
    intros h hw [hev].
    apply peregrine_backend_ocaml in h as (opts & q & hbo & hq & hx).
    cbn in hq. injection hq as <-.
    exists opts. split; [exact hbo|].
    pose proof (proj1 (OCamlBackend.extract_ocaml_warnings _ _ _ _ _ _ _ hx) hw) as hc.
    split.
    - unfold OCamlBackend.extract_ocaml in hx. injection hx as _ <-. reflexivity.
    - apply (ocaml_pipeline_correct _ v hc). constructor. exact (eval_fill_axioms _ _ _ hev).
  Qed.

  (** ** End-to-end theorems *)

  (** Untyped input: if the input file is the serialization of an untyped
      program [p0] that evaluates to a saturated first-order value [v], and
      Peregrine with the OCaml backend produces [out] without warning, then
      [out] is correct for the value [v_c] of the program handed to the
      backend ([peregrine_untyped_fo]). *)
  Theorem peregrine_untyped_ocaml {guard : PCUICWfEnvImpl.abstract_guard_impl}
      c attrs ir io lbox p0 env t c' p' file warnings out v :
    let f := NameSanitize.get_sanitizer c' in
    let env_s := rename_env (NameSanitize.sanitized_kername f) (sanitized_name f) (sanitized_ident f) env in
    let v_s := rename (NameSanitize.sanitized_kername f) (sanitized_name f) v in
    let econf := mk_opts c' false (fun _ => None) in
    let m := mk_cstr_reorders c' in
    let unb := econf.(enable_unsafe).(unboxing) in
    let v_c := fo_value_compile m env_s unb c'.(erasure_opts).(implement_box) v_s in
    p0 = Untyped env (Some t) ->
    strings_ok p0 = true ->
    peregrine_middle_end_string c attrs ir io lbox (Serialize.string_of_PAst p0) = Ok (c', p') ->
    peregrine_backend c' p' file = Ok (warnings, OCamlProgram out) ->
    warnings = [] ->
    fo_sat (fo_arity env) v ->
    (remap_on econf = true -> remap_fo econf (fo_unboxed_value m env_s unb v_s)) ->
    eval_eprogram default_wcbv_flags (env, t) v ->
    exists env' t' opts, p' = Untyped env' (Some t') /\ c'.(backend_opts) = OCaml opts /\
      ocaml_output_correct c'.(const_remappings_opts) opts.(Config.program_type) env' t' out v_c.
  Proof.
    intros f env_s v_s econf m unb v_c hp hs hme hb hw hsat hremap hev.
    have hnt : needs_typed c' = false.
    { apply peregrine_backend_ocaml in hb as (opts & _ & hbo & _). unfold needs_typed. now rewrite hbo. }
    destruct (peregrine_untyped_fo c attrs ir io lbox p0 env t c' p' v hp hs hme hnt hsat hremap hev)
      as (env' & t' & -> & hev').
    destruct (ocaml_backend_correct c' env' t' file warnings out _ hb hw hev') as (opts & hbo & hok).
    now exists env', t', opts.
  Qed.

  (** Typed input, see [peregrine_typed_untyped_fo]. *)
  Theorem peregrine_typed_ocaml {guard : PCUICWfEnvImpl.abstract_guard_impl}
      c attrs ir io lbox p0 env t c' p' file warnings out v :
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
    peregrine_backend c' p' file = Ok (warnings, OCamlProgram out) ->
    warnings = [] ->
    fo_sat (fo_arity (ExAst.trans_env env)) v ->
    (forall env_s, NameSanitize.sanitize_typed_env f env = Ok env_s ->
     remap_on (econf env_s) = true -> forall pf,
     remap_fo (econf env_s)
       (fo_unboxed_value m (typed_dearged_env (econf env_s) m (q env_s) pf) unb
          (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s))) ->
    eval_typed_eprogram default_wcbv_flags (drop_bodies (fun kn => remapped c' (sk kn)) env, t) v ->
    exists env_s env' t' opts,
      NameSanitize.sanitize_typed_env f env = Ok env_s /\
      p' = Untyped env' (Some t') /\ c'.(backend_opts) = OCaml opts /\
      exists pf,
        ocaml_output_correct c'.(const_remappings_opts) opts.(Config.program_type) env' t' out
          (fo_value_compile m (typed_dearged_env (econf env_s) m (q env_s) pf) unb
             c'.(erasure_opts).(implement_box)
             (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s)).
  Proof.
    intros f sk v_s econf m unb q hp hs hme hb hw hsat hremap hev.
    have hnt : needs_typed c' = false.
    { apply peregrine_backend_ocaml in hb as (opts & _ & hbo & _). unfold needs_typed. now rewrite hbo. }
    destruct (peregrine_typed_untyped_fo c attrs ir io lbox p0 env t c' p' v hp hs hme hnt hsat hremap hev)
      as (env_s & env' & t' & he & -> & pf & hev').
    destruct (ocaml_backend_correct c' env' t' file warnings out _ hb hw hev') as (opts & hbo & hok).
    exists env_s, env', t', opts. split; [exact he|]. split; [reflexivity|]. split; [exact hbo|].
    now exists pf.
  Qed.
End OCamlOutput.
