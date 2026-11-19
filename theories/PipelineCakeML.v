(** * End-to-end correctness of Peregrine with the CakeML backend

    This file composes the first-order results of the middle-end
    ([PipelineFirstOrder]) with the correctness of the CakeML backend
    ([CakeMLBackend.cakeml_pipeline_correct], which rests on
    [CakeML.Backend.CompileCorrect.compile_program_correct]).

    If the input file is the serialization of a program that evaluates to a
    saturated first-order value, Peregrine with the CakeML backend succeeds and
    reports no warning, then the printed output is the serialization of the
    compiled CakeML program, and for every run of its declarations
    ([CompileCorrect.eval_program_decls]) the main expression evaluates, in
    CakeML's big-step semantics ([CakeML.CakeML.bigstep.evaluate]), to a value
    related to the value that the middle-end theorem gives for the lambda-box
    program handed to the backend.  When that value is a constructor tree
    ([CakeMLBackend.fo_cstrb]), the CakeML value is its translation
    [CompileCorrect.compile_value].

    Covered: untyped input ([peregrine_untyped_cakeml]) and typed input
    ([peregrine_typed_cakeml]); the CakeML backend is untyped.

    Not covered by the proofs (trusted):
    - the printing of the CakeML AST as S-expressions and its parsing by the
      CakeML compiler, and the CakeML compiler itself;
    - the CakeML semantics is cakeml-backend's Rocq formalization of the
      big-step semantics of CakeML expressions; it has no declarations, so
      [CompileCorrect.eval_program_decls] models the emitted [Dtype] blocks
      after CakeML's [build_tdefs] (fresh type stamps, constructor names and
      arities; the placeholder argument types are ignored, and type inference,
      which [cake --skip_type_inference=true] skips, is not modelled) and the
      [Dlet]s as bindings of the values of their expressions;
    - the external realization of axioms: the correctness statement is about
      the program in which each axiom has the placeholder body [fun x => x]
      ([ExtractionCheck.fill_axioms]); the printed program instead refers to
      the external realization ([ExtractionCheck.restore_axioms]).  Without
      axioms the two coincide ([restore_axioms_nil]). *)

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
From MetaRocq.Erasure Require EWcbvEvalNamed.
From MetaRocq.Erasure.Typed Require ExAst.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From Peregrine Require Import EExtraFlags ERenameGlobals Transforms EFirstOrder EFirstOrderEta
  EFirstOrderCorrect EFirstOrderTyped NameSanitizeCorrect PipelineWf PipelineFirstOrder.
From Peregrine Require ExtractionCheck CakeMLBackend.
From CakeML.CakeML Require namespace bigstep.
From CakeML.Backend Require CompileCorrect PipelineCorrect.

Import MonadNotation.

(** [peregrine_pipeline] fails or is the middle-end followed by the backend. *)
Lemma peregrine_pipeline_gen_inv {guard : PCUICWfEnvImpl.abstract_guard_impl} c attrs ir io lbox s file r :
  peregrine_pipeline_gen c attrs ir io lbox s file = Ok r ->
  exists c' p', peregrine_middle_end_string c attrs ir io lbox s = Ok (c', p') /\
    peregrine_backend c' p' file = Ok r.
Proof.
  rewrite peregrine_pipeline_middle_end.
  destruct peregrine_middle_end_string as [[c' p']|e]; cbn; [|discriminate].
  intros h. now exists c', p'.
Qed.

Local Arguments CakeMLBackend.extract_cakeml : simpl never.

(** Only the CakeML backend produces CakeML programs. *)
Lemma peregrine_backend_cakeml c p file warnings out :
  peregrine_backend c p file = Ok (warnings, CakeMLProgram out) ->
  exists opts q, c.(backend_opts) = CakeML opts /\ PAst_to_EAst p = Ok q /\
    CakeMLBackend.extract_cakeml c.(const_remappings_opts) c.(custom_attributes_opts) opts file q
      = Ok (warnings, out).
Proof.
  unfold peregrine_backend, run_backend. intros h.
  destruct check_lowered; cbn in h; [|discriminate].
  destruct (backend_opts c) as [| | | | | |opts| | | | | |] eqn:hb; cbn -[CakeMLBackend.extract_cakeml] in h;
    repeat (match type of h with context [@bind _ _ _ _ ?x _] =>
              let e := fresh "e" in destruct x eqn:e end;
            cbn -[CakeMLBackend.extract_cakeml] in h);
    try discriminate.
  match goal with
  | e : PAst_to_EAst p = Ok ?q, e' : CakeMLBackend.extract_cakeml _ _ _ _ _ = Ok ?r |- _ =>
      exists opts, q; destruct r; injection h as -> ->; auto
  end.
Qed.

(** Without axioms, the printed program is the compiled one. *)
Lemma restore_axioms_nil {A} (l : list (string * option A)) :
  ExtractionCheck.restore_axioms [] l = l.
Proof.
  unfold ExtractionCheck.restore_axioms.
  induction l as [|[n b] l IH]; cbn; [reflexivity|]. now rewrite IH.
Qed.

(** The correctness of the CakeML output [out] for the lambda-box program
    [(env, t)] with value [v]: [out] prints the compiled program [cp] (with the
    axioms restored), and for every run of the declarations of [cp], the main
    expression of [cp] evaluates to a CakeML value related to a named value
    [vn] that represents [v]. *)
Definition cakeml_output_correct (env : global_declarations) (t : term)
    (out : list string * string) (v : term) : Prop :=
  let q := (ExtractionCheck.fill_axioms env, t) in
  let cp := CakeMLBackend.compile_cakeml q in
  out = CakeMLBackend.print_program (CakeMLBackend.extract_names t)
          (cp.1.1, ExtractionCheck.restore_axioms (ExtractionCheck.axiom_names env) cp.1.2, cp.2) /\
  exists vn, ∥ EWcbvEvalNamed.represents_value vn v ∥ /\
    forall n0 env0 genv,
      CompileCorrect.eval_program_decls n0 env0 cp.1 genv ->
      exists w, bigstep.evaluate genv cp.2 (namespace.Rval w) /\
        CompileCorrect.vrel (CakeMLBackend.annotate_program q).1 (namespace.c _ genv)
          (CompileCorrect.type_stamp n0 (CakeMLBackend.annotate_program q).1) vn w.

(** On constructor trees, the CakeML value is [CompileCorrect.compile_value]. *)
Lemma cakeml_output_correct_fo env t out v :
  cakeml_output_correct env t out v ->
  CakeMLBackend.fo_cstrb v = true ->
  let q := (ExtractionCheck.fill_axioms env, t) in
  let cp := CakeMLBackend.compile_cakeml q in
  forall n0 env0 genv,
    CompileCorrect.eval_program_decls n0 env0 cp.1 genv ->
    bigstep.evaluate genv cp.2
      (namespace.Rval (CompileCorrect.compile_value (CakeMLBackend.annotate_program q).1 n0
                         (PipelineCorrect.eval_fo v))).
Proof.
  intros [_ (vn & [hr] & h)] hfo; cbv zeta; intros n0 env0 genv hd.
  destruct (CakeMLBackend.represents_value_fo_cstr v vn hfo hr) as [-> hfvn].
  destruct (h n0 env0 genv hd) as (w & hw & hrel).
  pose proof (CompileCorrect.vrel_fo _ n0 _ _ _ hfvn hrel) as e.
  rewrite e in hw. exact hw.
Qed.

(** The CakeML backend is correct on lambda-box programs for which it reports
    no warning. *)
Lemma cakeml_backend_correct c env t file warnings out v :
  peregrine_backend c (Untyped env (Some t)) file = Ok (warnings, CakeMLProgram out) ->
  warnings = [] ->
  eval_eprogram final_wcbv_flags (env, t) v ->
  cakeml_output_correct env t out v.
Proof.
  intros h hw [hev].
  apply peregrine_backend_cakeml in h as (opts & q & _ & hq & hx).
  cbn in hq. injection hq as <-.
  pose proof (proj1 (CakeMLBackend.extract_cakeml_warnings _ _ _ _ _ _ _ hx) hw) as hc.
  split.
  - cbv beta iota zeta delta [CakeMLBackend.extract_cakeml CakeMLBackend.compile_cakeml
      Compile.compile_program CakeMLBackend.annotate_program] in hx |- *.
    cbn [fst snd] in hx |- *.
    injection hx as _ <-. reflexivity.
  - apply (CakeMLBackend.cakeml_pipeline_correct _ v hc).
    constructor. exact (ExtractionCheck.eval_fill_axioms env t v hev).
Qed.

(** ** End-to-end theorems *)

(** Untyped input: if the input file is the serialization of an untyped program
    [p0] that evaluates to a saturated first-order value [v], and Peregrine with
    the CakeML backend produces [out] without warning, then [out] is correct
    for the value [v_c] of the program handed to the backend
    ([peregrine_untyped_fo]). *)
Theorem peregrine_untyped_cakeml {guard : PCUICWfEnvImpl.abstract_guard_impl}
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
  peregrine_backend c' p' file = Ok (warnings, CakeMLProgram out) ->
  warnings = [] ->
  fo_sat (fo_arity env) v ->
  (remap_on econf = true -> remap_fo econf (fo_unboxed_value m env_s unb v_s)) ->
  eval_eprogram default_wcbv_flags (env, t) v ->
  exists env' t', p' = Untyped env' (Some t') /\ cakeml_output_correct env' t' out v_c.
Proof.
  intros f env_s v_s econf m unb v_c hp hs hme hb hw hsat hremap hev.
  have hnt : needs_typed c' = false.
  { apply peregrine_backend_cakeml in hb as (opts & _ & hbo & _). unfold needs_typed. now rewrite hbo. }
  destruct (peregrine_untyped_fo c attrs ir io lbox p0 env t c' p' v hp hs hme hnt hsat hremap hev)
    as (env' & t' & -> & hev').
  exists env', t'. split; [reflexivity|].
  exact (cakeml_backend_correct c' env' t' file warnings out _ hb hw hev').
Qed.

(** Typed input, see [peregrine_typed_untyped_fo]. *)
Theorem peregrine_typed_cakeml {guard : PCUICWfEnvImpl.abstract_guard_impl}
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
  peregrine_backend c' p' file = Ok (warnings, CakeMLProgram out) ->
  warnings = [] ->
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
      cakeml_output_correct env' t' out
        (fo_value_compile m (typed_dearged_env (econf env_s) m (q env_s) pf) unb
           c'.(erasure_opts).(implement_box)
           (fo_dearg (typed_dearg_masks (econf env_s) m (q env_s) pf) v_s)).
Proof.
  intros f sk v_s econf m unb q hp hs hme hb hw hsat hremap hev.
  have hnt : needs_typed c' = false.
  { apply peregrine_backend_cakeml in hb as (opts & _ & hbo & _). unfold needs_typed. now rewrite hbo. }
  destruct (peregrine_typed_untyped_fo c attrs ir io lbox p0 env t c' p' v hp hs hme hnt hsat hremap hev)
    as (env_s & env' & t' & he & -> & pf & hev').
  exists env_s, env', t'. split; [exact he|]. split; [reflexivity|]. exists pf.
  exact (cakeml_backend_correct c' env' t' file warnings out _ hb hw hev').
Qed.
