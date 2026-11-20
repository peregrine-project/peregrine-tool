(** * A non-vacuity instance of [PipelineOCaml.peregrine_untyped_ocaml]

    The untyped program [negb false] over a two-constructor inductive [bool]:
    the middle-end and the OCaml backend are run by [vm_compute], the input
    evaluation is derived by hand, and the conclusion of the theorem gives
    the evaluation of the compiled Malfunction main term to the
    Malfunction value of [true]. *)

From Stdlib Require Import List ssreflect ssrbool.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From MetaRocq.Common Require Import Kernames BasicAst Universes.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWcbvEval EProgram.
From MetaRocq.Erasure Require EWcbvEvalNamed.
From MetaRocq.SafeChecker Require PCUICWfEnvImpl.
From MetaRocq.ErasurePlugin Require Erasure.
From Peregrine Require Import PAst Config ConfigUtils ELboxOpts AutoInlining Pipeline PipelineFirstOrder.
From Peregrine Require Import EFirstOrder EFirstOrderEta Serialize SerializeRoundtrip SerializeConfig SerializePAst.
From Peregrine Require PipelineOCaml OCamlBackend ExtractionCheck.
From Malfunction Require SemanticsSpec CompileCorrect PipelineCorrect.

Import ListNotations.
Local Open Scope bs_scope.

Module Ex.
  Definition mp : modpath := MPfile ["Ex"].
  Definition bool_ind : inductive := {| inductive_mind := (mp, "bool"); inductive_ind := 0 |}.
  Definition tt_ : term := tConstruct bool_ind 0 [].
  Definition ff_ : term := tConstruct bool_ind 1 [].

  Definition bool_decl : global_decl :=
    InductiveDecl {| ind_finite := Finite; ind_npars := 0;
      ind_bodies := [ {| ind_name := "bool"; ind_propositional := false; ind_kelim := IntoAny;
                         ind_ctors := [ {| cstr_name := "true"; cstr_nargs := 0 |};
                                        {| cstr_name := "false"; cstr_nargs := 0 |} ];
                         ind_projs := [] |} ] |}.

  Definition negb_body : term :=
    tLambda (nNamed "b") (tCase (bool_ind, 0) (tRel 0) [([], ff_); ([], tt_)]).

  Definition env : PAst.untyped_env :=
    [ ((mp, "negb"), ConstantDecl {| cst_body := Some negb_body |});
      ((mp, "bool"), bool_decl) ].

  Definition t : term := tApp (tConst (mp, "negb")) ff_.
  Definition p0 : PAst := Untyped env (Some t).

  Lemma eval_t : @eval_eprogram default_wcbv_flags (env, t) tt_.
  Proof.
    constructor. cbn.
    eapply eval_beta.
    - eapply eval_delta; [reflexivity|reflexivity|]. now apply eval_atom.
    - now apply eval_atom.
    - cbn. eapply (eval_iota _ _ _ {| cstr_name := "false"; cstr_nargs := 0 |} _ 1 []);
        [reflexivity| |reflexivity|reflexivity|reflexivity|reflexivity|].
      + now apply eval_atom.
      + now apply eval_atom.
  Qed.

  Definition c : string + ConfigUtils.config' := inr (ConfigUtils.empty_config' (ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config')).
  Definition io : inline_opts :=
    {| inline_standard := false; inline_small := false; inline_size_limit := 12; inline_excluded := [] |}.

  Definition middle :=
    @peregrine_middle_end_string Erasure.fake_guard_impl c [] false io no_lbox_opts
      (Serialize.string_of_PAst p0).

  Definition res := Eval vm_compute in middle.
  Definition c' : config :=
    Eval vm_compute in match res with Ok r => r.1 | Err _ => mk_config (empty_config' (OCaml' empty_ocaml_config')) end.
  Definition p' : PAst := Eval vm_compute in match res with Ok r => r.2 | Err _ => Untyped [] None end.

  Lemma hme : middle = Ok (c', p').
  Proof. vm_compute. reflexivity. Qed.

  Definition file : string := "ex".
  Definition bres := Eval vm_compute in peregrine_backend c' p' file.
  Definition out : list string * string :=
    Eval vm_compute in match bres with Ok (_, OCamlProgram o) => o | _ => ([], "") end.

  Lemma hb : peregrine_backend c' p' file = Ok ([], OCamlProgram out).
  Proof. vm_compute. reflexivity. Qed.

  Definition env' : global_declarations :=
    Eval vm_compute in match p' with Untyped e _ => e | _ => [] end.
  Definition t' : term := Eval vm_compute in match p' with Untyped _ (Some t) => t | _ => tBox end.

  (** The program compiled by the backend, its named environment, its
      Malfunction main term and the value of the input program after the
      middle-end. *)
  Definition q0 : EAst.program := (ExtractionCheck.fill_axioms env', t').
  Definition Σn := Eval vm_compute in PipelineOCaml.annotated_env q0.
  Definition main := Eval vm_compute in (OCamlBackend.compile_ocaml q0).2.

  Lemma strings_ok_p0 : SerializeRoundtrip.strings_ok p0 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fo_sat_tt : fo_sat (EFirstOrderEta.fo_arity env) tt_.
  Proof. apply (fo_sat_construct _ bool_ind 0 []); [vm_compute; constructor|constructor]. Qed.

  Section Inst.
    Local Existing Instance Malfunction.SemanticsSpec.CanonicalPointer.
    Local Existing Instance Malfunction.SemanticsSpec.CanonicalHeap.

    (** The Malfunction value of [true]. *)
    Definition vval := Eval vm_compute in
      Malfunction.CompileCorrect.compile_value Σn (Malfunction.PipelineCorrect.eval_fo tt_).

    (** The instance: for every value environment [Σ'] of the global
        definitions, the compiled main term [main] evaluates to [vval]. *)
    Theorem ex_ocaml_eval Σ' :
      Malfunction.CompileCorrect.malfunction_env_prop Σn Σ' ->
      forall h, Malfunction.SemanticsSpec.eval Σ' Malfunction.SemanticsSpec.empty_locals h main h vval.
    Proof.
      intros hΣ' h.
      destruct (@PipelineOCaml.peregrine_untyped_ocaml _ _ Erasure.fake_guard_impl
                  c [] false io no_lbox_opts p0 env t c' p' file [] out tt_
                  eq_refl strings_ok_p0 hme hb eq_refl fo_sat_tt)
        as (env'' & t'' & opts & hp & hbo & hok);
        [intros hr; vm_compute in hr; discriminate hr|exact eval_t|].
      unfold p' in hp. injection hp as <- <-.
      pose proof (PipelineOCaml.ocaml_output_correct_fo _ _ _ _ _ _ hok) as hfo.
      specialize (hfo ltac:(vm_compute; reflexivity)).
      exact (hfo Σ' hΣ' h).
    Qed.

    (** The hypothesis on [Σ'] is satisfiable: [negb] is bound to the
        Malfunction value of its closure. *)
    Definition negb_named := Eval vm_compute in
      match Σn with (_, ConstantDecl {| cst_body := Some b |}) :: _ => b | _ => tBox end.
    Definition Σex := Eval vm_compute in
      match negb_named with
      | tLambda (nNamed na) b =>
          [("Ex.negb", Malfunction.CompileCorrect.compile_value Σn (EWcbvEvalNamed.vClos na b []))]
      | _ => [] end.

    Lemma ex_env_prop : Malfunction.CompileCorrect.malfunction_env_prop Σn Σex.
    Proof.
      intros kn decl body v hd hb hev.
      unfold EGlobalEnv.declared_constant in hd. cbn in hd.
      match type of hd with (if ?b then _ else _) = _ => destruct b eqn:e end.
      2: { cbn in hd. repeat (match type of hd with (if ?b then _ else _) = _ => destruct b end);
           discriminate hd. }
      injection hd as <-. cbn in hb. injection hb as <-.
      inversion hev; subst. left.
      apply eqb_eq in e. subst kn. vm_compute. reflexivity.
    Qed.

    Corollary ex_ocaml_eval_ex h :
      Malfunction.SemanticsSpec.eval Σex Malfunction.SemanticsSpec.empty_locals h main h vval.
    Proof. exact (ex_ocaml_eval Σex ex_env_prop h). Qed.
  End Inst.
End Ex.

