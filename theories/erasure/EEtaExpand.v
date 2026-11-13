(** * Eta-expansion of λ□ programs

    MetaRocq's erasure pipeline requires its input to be eta-expanded in the
    sense of [EEtaExpandedFix.expanded]: a fixpoint [tFix mfix idx] is applied
    to more than [rarg] arguments, a constructor to all its parameters and
    arguments, and a variable bound by a fixpoint to more than the [rarg] of
    its definition.  Rocq's erasure produces such programs, since the program
    is eta-expanded before erasure; other frontends (Agda, Lean) need not.

    [eta_expand_program] establishes the property.  It wraps every
    under-applied head [h] (fixpoint, constructor, or fixpoint-bound variable)
    of required arity [n] in [n] abstractions, [fun x1 .. xn => h x1 .. xn]
    ([eta_wrap]), and leaves its arguments in place.  It is the identity on
    eta-expanded terms.

    This file defines the transformation and proves that it preserves
    wellformedness ([eta_expand_program_wf]) and that its output is
    eta-expanded ([eta_expand_program_expanded]).  Evaluation is preserved by
    EEtaExpandSim.v. *)

From Stdlib Require Import List Arith Lia ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWellformed EProgram.
From MetaRocq.Erasure Require EEtaExpandedFix.
From Equations Require Import Equations.

Import ListNotations.

Fixpoint mk_lams (n : nat) (t : term) : term :=
  match n with
  | 0 => t
  | S n => tLambda nAnon (mk_lams n t)
  end.

(** [tRel (n-1); ..; tRel 0] *)
Fixpoint rels_down (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => tRel n :: rels_down n
  end.

(** [fun x1 .. xn => t x1 .. xn] *)
Definition eta_wrap (n : nat) (t : term) : term :=
  mk_lams n (mkApps (lift0 n t) (rels_down n)).

Section Eta.
  Context (Σ : global_declarations).

  (** [Γ] gives, for every variable, the number of arguments it must be
      applied to: [S rarg] for a variable bound by a fixpoint, [0] otherwise.
      [napp] is the number of arguments the term is applied to. *)
  Fixpoint eta (Γ : list nat) (napp : nat) (t : term) {struct t} : term :=
    match t with
    | tRel i =>
      match nth_error Γ i with
      | Some m => if napp <? m then eta_wrap m t else t
      | None => t
      end
    | tEvar n args => tEvar n (map (eta Γ 0) args)
    | tLambda na b => tLambda na (eta (0 :: Γ) 0 b)
    | tLetIn na b b' => tLetIn na (eta Γ 0 b) (eta (0 :: Γ) 0 b')
    | tApp u v => tApp (eta Γ (S napp) u) (eta Γ 0 v)
    | tConstruct ind c args =>
      let t' := tConstruct ind c (map (eta Γ 0) args) in
      match args, lookup_constructor_pars_args Σ ind c with
      | [], Some (p, a) => if napp <? p + a then eta_wrap (p + a) t' else t'
      | _, _ => t'
      end
    | tCase ci d brs =>
      tCase ci (eta Γ 0 d) (map (fun br => (br.1, eta (repeat 0 #|br.1| ++ Γ) 0 br.2)) brs)
    | tProj p c => tProj p (eta Γ 0 c)
    | tFix mfix idx =>
      let Γ' := rev_map (fun d => S d.(rarg)) mfix ++ Γ in
      let t' := tFix (map (map_def (eta Γ' 0)) mfix) idx in
      match nth_error mfix idx with
      | Some d => if napp <=? d.(rarg) then eta_wrap (S d.(rarg)) t' else t'
      | None => t'
      end
    | tCoFix mfix idx => tCoFix (map (map_def (eta (repeat 0 #|mfix| ++ Γ) 0)) mfix) idx
    | tPrim p => tPrim (map_prim (eta Γ 0) p)
    | tLazy t => tLazy (eta Γ 0 t)
    | tForce t => tForce (eta Γ 0 t)
    | tBox | tVar _ | tConst _ => t
    end.

  Definition eta_constant_decl (cb : constant_body) : constant_body :=
    {| cst_body := option_map (eta [] 0) cb.(cst_body) |}.

  Definition eta_decl (d : global_decl) : global_decl :=
    match d with
    | ConstantDecl cb => ConstantDecl (eta_constant_decl cb)
    | InductiveDecl idecl => d
    end.
End Eta.

Definition eta_expand_env (Σ : global_declarations) : global_declarations :=
  map (on_snd (eta_decl Σ)) Σ.

Definition eta_expand_program (p : program) : program :=
  (eta_expand_env p.1, eta p.1 [] 0 p.2).

(** ** Basic facts *)

Definition eta_env_gen (Σ0 Σ : global_declarations) : global_declarations :=
  map (on_snd (eta_decl Σ0)) Σ.

Lemma lookup_env_eta_env_gen Σ0 Σ kn :
  lookup_env (eta_env_gen Σ0 Σ) kn = option_map (eta_decl Σ0) (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; auto.
  destruct (eqb_spec kn kn'); auto.
Qed.

Lemma lookup_minductive_eta_env_gen Σ0 Σ kn :
  lookup_minductive (eta_env_gen Σ0 Σ) kn = lookup_minductive Σ kn.
Proof.
  rewrite /lookup_minductive lookup_env_eta_env_gen.
  destruct lookup_env as [[]|]; cbn; auto.
Qed.

Lemma lookup_constant_eta_env_gen Σ0 Σ kn :
  lookup_constant (eta_env_gen Σ0 Σ) kn = option_map (eta_constant_decl Σ0) (lookup_constant Σ kn).
Proof.
  rewrite /lookup_constant lookup_env_eta_env_gen.
  destruct lookup_env as [[]|]; cbn; auto.
Qed.

Lemma lookup_inductive_eta_env_gen Σ0 Σ ind :
  lookup_inductive (eta_env_gen Σ0 Σ) ind = lookup_inductive Σ ind.
Proof. now rewrite /lookup_inductive lookup_minductive_eta_env_gen. Qed.

Lemma lookup_constructor_eta_env_gen Σ0 Σ ind c :
  lookup_constructor (eta_env_gen Σ0 Σ) ind c = lookup_constructor Σ ind c.
Proof. now rewrite /lookup_constructor lookup_inductive_eta_env_gen. Qed.

Lemma lookup_projection_eta_env_gen Σ0 Σ p :
  lookup_projection (eta_env_gen Σ0 Σ) p = lookup_projection Σ p.
Proof. now rewrite /lookup_projection lookup_constructor_eta_env_gen. Qed.

Lemma rels_down_length n : #|rels_down n| = n.
Proof. induction n; cbn; congruence. Qed.

Lemma rev_map_rarg_map (f : term -> term) (g : def term -> nat) mfix :
  (forall d, g (map_def f d) = g d) ->
  rev_map g (map (map_def f) mfix) = rev_map g mfix.
Proof.
  intros Hg. rewrite !rev_map_spec map_map. f_equal. now apply map_ext.
Qed.

Lemma eta_wrap_0 t : eta_wrap 0 t = t.
Proof. rewrite /eta_wrap /=. apply lift0_id. Qed.

(** ** Wellformedness *)

Section Wf.
  Context {efl : EEnvFlags}.
  Context (hlam : has_tLambda) (happ : has_tApp) (hrel : has_tRel).
  Context (hblocks : cstr_as_blocks = false).

  Lemma wellformed_mk_lams Σ n k t :
    wellformed Σ (n + k) t -> wellformed Σ k (mk_lams n t).
  Proof using hlam.
    induction n in k |- *; cbn; auto.
    intros H. rewrite hlam /=. apply IHn. now rewrite Nat.add_succ_r.
  Qed.

  Lemma wellformed_rels_down Σ n k : forallb (wellformed Σ (n + k)) (rels_down n).
  Proof using hrel.
    assert (H : forall m, n <= m -> forallb (wellformed Σ m) (rels_down n)).
    { induction n; cbn; auto. intros m Hm. rewrite hrel /= IHn; [lia|].
      rewrite andb_true_r. apply Nat.ltb_lt. lia. }
    apply H. lia.
  Qed.

  Lemma wellformed_eta_wrap Σ n k t :
    wellformed Σ k t -> wellformed Σ k (eta_wrap n t).
  Proof using hlam happ hrel.
    intros H. apply wellformed_mk_lams.
    rewrite wellformed_mkApps // wellformed_rels_down andb_true_r.
    rewrite Nat.add_comm. now apply wellformed_lift.
  Qed.

  Lemma eta_isLambda Σ0 Γ napp t : isLambda t -> isLambda (eta Σ0 Γ napp t).
  Proof. destruct t; cbn; auto. Qed.

  Lemma eta_wellformed Σ0 Σ t k Γ napp :
    wellformed Σ k t -> wellformed (eta_env_gen Σ0 Σ) k (eta Σ0 Γ napp t).
  Proof using hlam happ hrel hblocks.
    induction t in k, Γ, napp |- * using term_forall_list_ind; cbn [eta]; intros wf.
    all: try (cbn in wf |- *; rtoProp; intuition (solve_all; eauto); fail).
    - destruct nth_error; [destruct Nat.ltb|]; auto.
      now apply wellformed_eta_wrap.
    - cbn in wf |- *. rewrite /lookup_constant lookup_env_eta_env_gen.
      rewrite /lookup_constant in wf.
      destruct lookup_env as [[[[]]|]|]; cbn in *; rtoProp; intuition auto.
    - cbn -[lookup_constructor lookup_constructor_pars_args] in wf. rewrite hblocks in wf. rtoProp. destruct args; [|easy].
      assert (wf' : wellformed (eta_env_gen Σ0 Σ) k (tConstruct i n [])).
      { cbn -[lookup_constructor lookup_constructor_pars_args]. rewrite hblocks lookup_constructor_eta_env_gen. rtoProp; intuition auto. }
      cbn [map]. destruct lookup_constructor_pars_args as [[p a]|]; auto.
      destruct Nat.ltb; auto. now apply wellformed_eta_wrap.
    - cbn -[lookup_inductive] in wf |- *. rtoProp. repeat split; auto.
      + now rewrite /wf_brs lookup_inductive_eta_env_gen length_map.
      + solve_all.
    - cbn -[lookup_projection] in wf |- *. rewrite lookup_projection_eta_env_gen. rtoProp; intuition auto.
    - assert (wf' : wellformed (eta_env_gen Σ0 Σ) k
        (tFix (map (map_def (eta Σ0 (rev_map (fun d => S (rarg d)) m ++ Γ) 0)) m) n)).
      { cbn in wf |- *. move/andP: wf => [/andP [hfix hl] hwf]. rewrite hfix /=. apply/andP; split.
        - rewrite forallb_map. solve_all. now apply eta_isLambda.
        - rewrite /wf_fix_gen length_map. move/andP: hwf => [-> hb] /=. solve_all. now apply a. }
      destruct nth_error; [destruct Nat.leb|]; auto. now apply wellformed_eta_wrap.
    - cbn in wf |- *. move/andP: wf => [-> hwf] /=.
      rewrite /wf_fix_gen length_map. move/andP: hwf => [-> hb] /=. solve_all. now apply a.
    - cbn in wf |- *. rewrite has_prim_map_prim. rtoProp. split; [intuition auto|]. solve_all.
      depelim H1; cbn; constructor. destruct p as [[IHd wd] IHv]. split; cbn; [now apply IHd|]. solve_all.
  Qed.

  Lemma fresh_global_eta_env_gen Σ0 Σ kn : fresh_global kn Σ -> fresh_global kn (eta_env_gen Σ0 Σ).
  Proof. rewrite /fresh_global /eta_env_gen. intros H. solve_all. Qed.

  Lemma eta_env_gen_wf Σ0 Σ : wf_glob Σ -> wf_glob (eta_env_gen Σ0 Σ).
  Proof using hlam happ hrel hblocks.
    induction 1; cbn; constructor; auto.
    - destruct d as [[[b|]]|]; cbn in *; auto. now apply eta_wellformed.
    - now apply fresh_global_eta_env_gen.
  Qed.

  Theorem eta_expand_program_wf (p : eprogram) :
    wf_eprogram efl p -> wf_eprogram efl (eta_expand_program p).
  Proof using hlam happ hrel hblocks.
    intros [wfe wft]. split; cbn.
    - now apply eta_env_gen_wf.
    - now apply eta_wellformed.
  Qed.
End Wf.

(** ** The output is eta-expanded *)

Import EEtaExpandedFix.

Lemma lookup_constructor_declared_constructor Σ ind c mdecl idecl cdecl :
  lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
  declared_constructor Σ (ind, c) mdecl idecl cdecl.
Proof.
  rewrite /lookup_constructor /lookup_inductive /lookup_minductive.
  rewrite /declared_constructor /declared_inductive /declared_minductive /=.
  destruct lookup_env as [[]|] => //=.
  destruct (nth_error (ind_bodies _) _) eqn:E1 => //=.
  destruct (nth_error (ind_ctors _) _) eqn:E2 => //=.
  intros [= <- <- <-]. auto.
Qed.

Lemma expanded_mk_lams Σ n Γ t :
  expanded Σ (repeat 0 n ++ Γ) t -> expanded Σ Γ (mk_lams n t).
Proof.
  induction n in Γ |- *; cbn; auto.
  intros H. constructor. apply IHn.
  change (expanded Σ ((0 :: repeat 0 n) ++ Γ) t) in H.
  now rewrite (repeat_cons n 0) -app_assoc in H.
Qed.

Lemma expanded_rels_down Σ n Γ :
  Forall (expanded Σ (repeat 0 n ++ Γ)) (rels_down n).
Proof.
  assert (H : forall m, m <= n -> Forall (expanded Σ (repeat 0 n ++ Γ)) (rels_down m)).
  { induction m; cbn; constructor; [|apply IHm; lia].
    eapply (expanded_tRel_app _ _ _ [] 0); [|cbn; lia|constructor].
    rewrite nth_error_app1 ?repeat_length //. now apply nth_error_repeat. }
  now apply H.
Qed.

(** Wrapping a head that is expanded once applied to [n] arguments *)
Lemma expanded_eta_wrap Σ n Γ h :
  (forall args, #|args| = n -> Forall (expanded Σ (repeat 0 n ++ Γ)) args ->
     expanded Σ (repeat 0 n ++ Γ) (mkApps (lift0 n h) args)) ->
  expanded Σ Γ (eta_wrap n h).
Proof.
  intros H. apply expanded_mk_lams, H; [apply rels_down_length|apply expanded_rels_down].
Qed.

Lemma expanded_mkApps_lambda Σ Γ f args :
  isLambda f -> expanded Σ Γ f -> Forall (expanded Σ Γ) args -> expanded Σ Γ (mkApps f args).
Proof.
  intros Hl Hf Ha. apply expanded_mkApps; auto. now destruct f.
Qed.

Lemma eta_wrap_isLambda n t : 0 < n -> isLambda (eta_wrap n t).
Proof. destruct n; [lia|reflexivity]. Qed.

Lemma expanded_lift Σ Γ Γ' Γ'' t :
  expanded Σ (Γ'' ++ Γ) t -> expanded Σ (Γ'' ++ Γ' ++ Γ) (lift #|Γ'| #|Γ''| t).
Proof.
  intros H. apply isEtaExp_expanded, isEtaExp_lift. now apply expanded_isEtaExp.
Qed.

Section Expanded.
  Context {efl : EEnvFlags}.
  Context (hblocks : cstr_as_blocks = false).
  (** [Σ] is the environment the term is wellformed in, [Σ0] the one
      constructors are looked up in, and [Σ'] the target environment. *)
  Context (Σ0 Σ Σ' : global_declarations).
  Context (Hctor0 : forall ind c b, lookup_constructor Σ ind c = Some b -> lookup_constructor Σ0 ind c = Some b).
  Context (Hctor' : forall ind c, lookup_constructor Σ' ind c = lookup_constructor Σ ind c).

  Lemma eta_expanded t Γ napp args :
    wellformed Σ #|Γ| t ->
    Forall (expanded Σ' Γ) args -> napp <= #|args| ->
    expanded Σ' Γ (mkApps (eta Σ0 Γ napp t) args).
  Proof using hblocks Hctor0 Hctor'.
    induction t in Γ, napp, args |- * using term_forall_list_ind; cbn [eta]; intros wf Hargs Hnapp.
    all: try lazymatch goal with
      | |- expanded _ _ (mkApps (tApp _ _) _) => idtac
      | |- _ => eapply expanded_mkApps; [reflexivity| |assumption]
      end.
    all: try (constructor; fail).
    - (* tRel *)
      cbn in wf. move/andP: wf => [_ /Nat.ltb_lt wf].
      destruct (nth_error Γ n) as [m|] eqn:E; [|apply nth_error_None in E; lia].
      destruct (Nat.ltb_spec napp m).
      + apply expanded_mkApps_lambda; [apply eta_wrap_isLambda; lia| |assumption].
        apply expanded_eta_wrap. intros args' Hlen Hargs'. cbn.
        eapply expanded_tRel_app; [|rewrite Hlen; reflexivity|assumption].
        rewrite nth_error_app2 repeat_length; [lia|].
        now replace (m + n - m) with n by lia.
      + eapply expanded_tRel_app; tea. lia.
    - (* tEvar *)
      cbn in wf. rtoProp. constructor. solve_all. now apply (a Γ 0 []).
    - (* tLambda *)
      cbn in wf. rtoProp. constructor. now apply (IHt (0 :: Γ) 0 []).
    - (* tLetIn *)
      cbn in wf. rtoProp. constructor; [now apply (IHt1 Γ 0 [])|now apply (IHt2 (0 :: Γ) 0 [])].
    - (* tApp *)
      cbn in wf. rtoProp. change (expanded Σ' Γ (mkApps (eta Σ0 Γ (S napp) t1) (eta Σ0 Γ 0 t2 :: args))).
      apply IHt1; [intuition auto| |cbn; lia].
      constructor; auto. apply (IHt2 Γ 0 []); intuition auto.
    - (* tConstruct *)
      cbn -[lookup_constructor lookup_constructor_pars_args] in wf. rewrite hblocks in wf.
      move/andP: wf => [/andP [_ hl] hnil]. destruct args0; [|easy]. cbn [map].
      destruct (lookup_constructor Σ i n) as [[[mdecl idecl] cdecl]|] eqn:E; [|easy].
      have E0 := Hctor0 _ _ _ E.
      have Hd : declared_constructor Σ' (i, n) mdecl idecl cdecl.
      { apply lookup_constructor_declared_constructor. now rewrite Hctor'. }
      rewrite /lookup_constructor_pars_args E0 /=.
      destruct (Nat.ltb_spec napp (ind_npars mdecl + cstr_nargs cdecl)).
      + apply expanded_mkApps_lambda; [apply eta_wrap_isLambda; lia| |assumption].
        apply expanded_eta_wrap. intros args' Hlen Hargs'. cbn.
        eapply expanded_tConstruct_app; tea. lia.
      + eapply expanded_tConstruct_app; tea. lia.
    - (* tCase *)
      cbn -[lookup_inductive] in wf. rtoProp. destruct p as [ind pars]. constructor.
      + apply (IHt Γ 0 []); intuition auto.
      + solve_all. apply (a (repeat 0 #|x.1| ++ Γ) 0 []); auto.
        now rewrite length_app repeat_length.
    - (* tProj *)
      cbn -[lookup_projection] in wf. rtoProp. constructor. apply (IHt Γ 0 []); intuition auto.
    - (* tFix *)
      cbn in wf. move/andP: wf => [/andP [_ hl] /andP [/Nat.ltb_lt hidx hwf]].
      set (Γ' := rev_map (fun d => S (rarg d)) m ++ Γ).
      set (m' := map (map_def (eta Σ0 Γ' 0)) m).
      have HΓ' : rev_map (fun d => 1 + rarg d) m' = rev_map (fun d => S (rarg d)) m.
      { subst m'. now rewrite rev_map_rarg_map. }
      have Hbodies : Forall (fun d => isLambda (dbody d) /\
          let ctx := rev_map (fun d => 1 + rarg d) m' in expanded Σ' (ctx ++ Γ) (dbody d)) m'.
      { cbn zeta. rewrite HΓ'. subst m'. apply Forall_map. solve_all.
        - now apply eta_isLambda.
        - apply (a Γ' 0 []); auto.
          now rewrite /Γ' length_app rev_map_spec List.length_rev length_map. }
      destruct (nth_error m n) as [d|] eqn:E; [|apply nth_error_None in E; lia].
      have E' : nth_error m' n = Some (map_def (eta Σ0 Γ' 0) d).
      { subst m'. now rewrite nth_error_map E. }
      destruct (Nat.leb_spec napp (rarg d)).
      + apply expanded_mkApps_lambda; [reflexivity| |assumption].
        apply expanded_eta_wrap. intros args' Hlen Hargs'. cbn [lift].
        eapply expanded_tFix.
        * cbn zeta. rewrite rev_map_rarg_map //. rewrite HΓ'.
          apply Forall_map. eapply Forall_impl; [exact Hbodies|].
          cbn. intros x [Hx1 Hx2]. split; [now destruct (dbody x)|].
          rewrite HΓ' in Hx2. rewrite length_map.
          have -> : #|m| + 0 = #|rev_map (fun d => S (rarg d)) m|
            by rewrite rev_map_spec List.length_rev length_map; lia.
          set (r := repeat 0 (S (rarg d))).
          have -> : S (rarg d) = #|r| by rewrite /r repeat_length.
          exact (expanded_lift Σ' Γ r _ (dbody x) Hx2).
        * assumption.
        * destruct args'; [discriminate|congruence].
        * rewrite nth_error_map E'. reflexivity.
        * cbn. lia.
      + eapply expanded_tFix; tea.
        * destruct args; [cbn in Hnapp; lia|congruence].
        * cbn. lia.
    - (* tCoFix *)
      cbn in wf. move/andP: wf => [_ /andP [_ hwf]]. constructor.
      rewrite length_map. apply Forall_map. solve_all.
      apply (a (repeat 0 #|m| ++ Γ) 0 []); auto.
      now rewrite length_app repeat_length.
    - (* tPrim *)
      cbn in wf. move/andP: wf => [_ hwf]. constructor.
      depelim X; cbn; constructor. destruct p as [IHd IHv]. cbn in hwf. move/andP: hwf => [hd hv].
      split; cbn; [now apply (IHd Γ 0 [])|]. solve_all. now apply (a0 Γ 0 []).
    - (* tLazy *)
      cbn in wf. rtoProp. constructor. apply (IHt Γ 0 []); intuition auto.
    - (* tForce *)
      cbn in wf. rtoProp. constructor. apply (IHt Γ 0 []); intuition auto.
  Qed.
End Expanded.

Lemma extends_tail kn d Σ Σ0 :
  fresh_global kn Σ -> extends ((kn, d) :: Σ) Σ0 -> extends Σ Σ0.
Proof.
  intros Hf Hext kn' decl Hl. apply Hext. cbn.
  destruct (eqb_spec kn' kn); auto. subst.
  now apply lookup_env_Some_fresh in Hl.
Qed.

Lemma eta_env_gen_expanded {efl : EEnvFlags} Σ0 Σ :
  cstr_as_blocks = false ->
  wf_glob Σ0 -> extends Σ Σ0 -> wf_glob Σ ->
  expanded_global_env (eta_env_gen Σ0 Σ).
Proof.
  intros hblocks wf0 Hext wf. induction wf; cbn; constructor.
  - apply IHwf. eapply extends_tail; tea.
  - destruct d as [[[b|]]|]; cbn in *; auto.
    have Hext' : extends Σ Σ0 by (eapply extends_tail; tea).
    apply (eta_expanded hblocks Σ0 Σ (eta_env_gen Σ0 Σ)
             (fun ind c b => extends_lookup_constructor wf0 Hext' ind c b)
             (lookup_constructor_eta_env_gen Σ0 Σ) b [] 0 []); auto.
Qed.

Theorem eta_expand_program_expanded {efl : EEnvFlags} (p : eprogram) :
  cstr_as_blocks = false ->
  wf_eprogram efl p -> expanded_eprogram (eta_expand_program p).
Proof.
  intros hblocks [wfe wft]. split; cbn.
  - apply eta_env_gen_expanded; auto. now intros ? ?.
  - apply (eta_expanded hblocks p.1 p.1 (eta_env_gen p.1 p.1) (fun _ _ _ H => H)
             (lookup_constructor_eta_env_gen p.1 p.1) p.2 [] 0 []); auto.
Qed.

(** ** Typed environments

    The typed pipelines work on [ExAst] environments, which are evaluated
    through [ExAst.trans_env]. Expanding the bodies of a typed environment
    commutes with [ExAst.trans_env]. *)

From MetaRocq.Erasure.Typed Require ExAst.
From MetaRocq.Erasure Require EReorderCstrs.

Definition eta_ex_decl (Σ0 : global_declarations) (d : ExAst.global_decl) : ExAst.global_decl :=
  match d with
  | ExAst.ConstantDecl cst =>
    ExAst.ConstantDecl {| ExAst.cst_type := ExAst.cst_type cst;
                          ExAst.cst_body := option_map (eta Σ0 [] 0) (ExAst.cst_body cst) |}
  | _ => d
  end.

Definition eta_expand_ex_env (Σ : ExAst.global_env) : ExAst.global_env :=
  map (on_snd (eta_ex_decl (ExAst.trans_env Σ))) Σ.

Definition eta_expand_typed_program (p : ExAst.global_env * term) : ExAst.global_env * term :=
  (eta_expand_ex_env p.1, eta (ExAst.trans_env p.1) [] 0 p.2).

Lemma trans_env_eta_ex_gen Σ0 Σ :
  ExAst.trans_env (map (on_snd (eta_ex_decl Σ0)) Σ) = eta_env_gen Σ0 (ExAst.trans_env Σ).
Proof.
  induction Σ as [|[[kn b] d] Σ IH]; cbn; auto.
  f_equal; auto. unfold on_snd; cbn. f_equal.
  destruct d as [cst|mib|[o|]]; cbn; auto.
Qed.

Lemma trans_env_eta_expand_ex_env Σ :
  ExAst.trans_env (eta_expand_ex_env Σ) = eta_expand_env (ExAst.trans_env Σ).
Proof. apply trans_env_eta_ex_gen. Qed.

Lemma wf_inductives_mapping_eta_expand_env Σ m :
  EReorderCstrs.wf_inductives_mapping Σ m ->
  EReorderCstrs.wf_inductives_mapping (eta_expand_env Σ) m.
Proof.
  unfold EReorderCstrs.wf_inductives_mapping, EReorderCstrs.wf_inductive_mapping.
  intros H. eapply forallb_impl; [|exact H]. intros [ind [na tags]] _.
  now rewrite (lookup_inductive_eta_env_gen Σ Σ).
Qed.
