(** Correctness of name sanitization.

    [sanitize_term] and [sanitize_untyped_env] compute the renaming [rename] of
    [ERenameGlobals], with [sanitized_kername f] on global names
    ([sanitize_spec]).  When [check_sanitized_injective] accepts the declared
    names, that renaming is injective on them, so sanitization preserves
    well-formedness and evaluation ([sanitize_correct]).  The configuration is
    renamed by the same function ([sanitize_config_spec]), so a declared name is
    in a renamed configuration list exactly when it was in the original one
    ([in_sanitized_iff], [find_sanitized]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils bytestring ResultMonad.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst EWellformed
  EWcbvEval EProgram.
From Peregrine Require Import Utils Unicode NameSanitize ERenameGlobals.
From Peregrine Require PAst Config.

Local Arguments sanitize_kername : simpl never.
Local Arguments sanitize_name : simpl never.
Local Arguments sanitize_inductive : simpl never.
Local Arguments sanitize_projection : simpl never.
Local Arguments monad_map_prim : simpl never.
Local Arguments of_string : simpl never.

Section Spec.
  Context (f : utf8_string -> string).

  Definition sanitized_name (na : name) : name :=
    match sanitize_name f na with Ok na' => na' | Err _ => na end.

  Definition sanitized_ident (s : ident) : ident :=
    match of_string s with Ok u => f u | Err _ => s end.

  Notation sk := (sanitized_kername f).
  Notation sn := sanitized_name.
  Notation si := sanitized_ident.
  Notation srename := (rename sk sn).

  Ltac inv_bind :=
    repeat match goal with
    | H : @bind _ _ _ _ _ _ = Ok _ |- _ => cbn in H
    | H : @ret _ _ _ _ = Ok _ |- _ => cbn in H
    | H : (match ?x with Ok _ => _ | Err _ => _ end) = Ok _ |- _ =>
        let e := fresh "e" in destruct x eqn:e; cbn in H; [|discriminate]
    | H : Ok _ = Ok _ |- _ => injection H as H; subst
    end.

  Lemma monad_map_spec {A B} (g : A -> result' B) (h : A -> B) l l' :
    All (fun x => forall y, g x = Ok y -> y = h x) l ->
    monad_map g l = Ok l' -> l' = map h l.
  Proof.
    induction 1 in l' |- *; cbn; intros H.
    - now injection H as <-.
    - inv_bind. f_equal; auto.
  Qed.

  Lemma monad_map_spec_all {A B} (g : A -> result' B) (h : A -> B) l l' :
    (forall x y, g x = Ok y -> y = h x) ->
    monad_map g l = Ok l' -> l' = map h l.
  Proof.
    intros hg. apply monad_map_spec. induction l; constructor; auto.
  Qed.

  Lemma sanitize_kername_spec kn kn' : sanitize_kername f kn = Ok kn' -> kn' = sk kn.
  Proof. rewrite /sanitized_kername => -> //. Qed.

  Lemma sanitize_name_spec na na' : sanitize_name f na = Ok na' -> na' = sn na.
  Proof. rewrite /sanitized_name => -> //. Qed.

  Lemma sanitize_inductive_spec i i' :
    sanitize_inductive f i = Ok i' -> i' = rename_inductive sk i.
  Proof.
    rewrite /sanitize_inductive. destruct (sanitize_kername f _) eqn:e; cbn; intros H; [|discriminate].
    injection H as <-. rewrite /rename_inductive /sanitized_kername e //.
  Qed.

  Lemma sanitize_projection_spec p p' :
    sanitize_projection f p = Ok p' -> p' = rename_projection sk p.
  Proof.
    rewrite /sanitize_projection. destruct (sanitize_inductive f _) eqn:e; cbn; intros H; [|discriminate].
    injection H as <-. rewrite /rename_projection (sanitize_inductive_spec _ _ e) //.
  Qed.

  Ltac use_specs :=
    repeat match goal with
    | e : sanitize_name f _ = Ok _ |- _ => apply sanitize_name_spec in e; subst
    | e : sanitize_kername f _ = Ok _ |- _ => apply sanitize_kername_spec in e; subst
    | e : sanitize_inductive f _ = Ok _ |- _ => apply sanitize_inductive_spec in e; subst
    | e : sanitize_projection f _ = Ok _ |- _ => apply sanitize_projection_spec in e; subst
    | e : monad_map (sanitize_name f) _ = Ok _ |- _ =>
      apply (monad_map_spec_all _ _ _ _ sanitize_name_spec) in e; subst
    | e : monad_map (sanitize_kername f) _ = Ok _ |- _ =>
      apply (monad_map_spec_all _ _ _ _ sanitize_kername_spec) in e; subst
    end.

  Ltac use_of_string :=
    rewrite /sanitized_ident; match goal with e : of_string _ = Ok _ |- _ => now rewrite e end.

  Lemma monad_map_prim_spec (g : term -> result' term) (h : term -> term) p p' :
    primProp (fun x => forall y, g x = Ok y -> y = h x) p ->
    monad_map_prim g p = Ok p' -> p' = map_prim h p.
  Proof.
    destruct 1; rewrite /monad_map_prim /=; intros H; inv_bind; try reflexivity.
    match goal with
    | hp : (forall y, Ok ?t = Ok y -> _) × All _ ?l, ev : monad_map g ?l = Ok _ |- _ =>
      destruct hp as [hd hv]; rewrite (hd t eq_refl) (monad_map_spec _ _ _ _ hv ev)
    end.
    reflexivity.
  Qed.

  Lemma sanitize_term_spec t t' : sanitize_term f t = Ok t' -> t' = srename t.
  Proof.
    induction t in t' |- * using term_forall_list_ind; cbn; intros H; inv_bind; cbn; auto.
    all: use_specs.
    all: try solve [f_equal; eauto].
    - f_equal. eapply monad_map_spec; tea.
    - f_equal. eapply monad_map_spec; tea.
    - destruct p as [ind n]. f_equal; eauto.
      eapply monad_map_spec; tea. solve_all.
      destruct x as [ns b]; cbn in *. inv_bind. use_specs. f_equal. eauto.
    - f_equal. eapply monad_map_spec; tea. solve_all. inv_bind. use_specs.
      rewrite /rename_def_with. f_equal. eauto.
    - f_equal. eapply monad_map_spec; tea. solve_all. inv_bind. use_specs.
      rewrite /rename_def_with. f_equal. eauto.
    - f_equal. eapply monad_map_prim_spec; tea.
      eapply primProp_impl; tea. cbn. intros x hx y hy. now apply hx.
  Qed.

  Lemma sanitize_global_decl_spec d d' :
    sanitize_global_decl f d = Ok d' -> d' = rename_decl sk sn si d.
  Proof.
    destruct d as [[b]|[fin np bodies]]; cbn; intros H; inv_bind.
    - destruct b; cbn in *; inv_bind; cbn; auto.
      match goal with e : sanitize_term f _ = Ok _ |- _ => now rewrite (sanitize_term_spec _ _ e) end.
    - rewrite /rename_mutual_inductive_body /=. do 2 f_equal.
      eapply monad_map_spec_all; tea. intros [] y h. cbn in h. inv_bind.
      rewrite /rename_one_inductive_body /=. f_equal.
      all: try solve [use_of_string].
      all: eapply monad_map_spec_all; tea; intros [] y' h'; cbn in h'; inv_bind;
        rewrite /rename_constructor_body /rename_projection_body /=; f_equal; use_of_string.
  Qed.

  Lemma sanitize_untyped_env_spec env env' :
    sanitize_untyped_env f env = Ok env' -> env' = rename_env sk sn si env.
  Proof.
    apply monad_map_spec_all. intros [kn d] y h. cbn in h. inv_bind. use_specs.
    match goal with e : sanitize_global_decl f _ = Ok _ |- _ =>
      now rewrite (sanitize_global_decl_spec _ _ e) end.
  Qed.

  (** * The injectivity check *)

  Lemma find_collision_spec (img : kername -> kername) l :
    find_collision img l = None ->
    forall x y, In x l -> In y l -> img x = img y -> x = y.
  Proof.
    induction l as [|kn l IH]; cbn => // hl x y hx hy e.
    destruct find eqn:hf => //.
    have hnone := find_none _ _ hf.
    have nocoll : forall z, In z l -> img kn = img z -> kn = z.
    { intros z hz ez. specialize (hnone z hz). cbn in hnone.
      change (eq_kername ?a ?b) with (eqb a b) in hnone.
      move: hnone. case: (eqb_spec kn z) => //= neq.
      rewrite ez. now rewrite eqb_refl. }
    destruct hx as [<-|hx], hy as [<-|hy]; auto.
    - symmetry. now apply nocoll.
  Qed.

  Lemma check_sanitized_injective_spec names :
    check_sanitized_injective f names = Ok tt -> injective_on sk names.
  Proof.
    rewrite /check_sanitized_injective. destruct find_collision as [[]|] eqn:h => // _.
    intros x y hx hy. now apply (find_collision_spec _ _ h).
  Qed.

  Lemma injective_on_incl names names' :
    injective_on sk names -> incl names' names -> injective_on sk names'.
  Proof. intros h hi x y hx hy. apply h; auto. Qed.

  (** * Correctness *)

  Theorem sanitize_correct {efl : EEnvFlags} {wfl : WcbvFlags} env t env' t' v extra :
    check_sanitized_injective f (untyped_env_names env ++ extra) = Ok tt ->
    sanitize_untyped_env f env = Ok env' ->
    sanitize_term f t = Ok t' ->
    wf_eprogram efl (env, t) ->
    eval env t v ->
    wf_eprogram efl (env', t') × eval env' t' (srename v).
  Proof.
    intros hc he ht wf ev.
    apply check_sanitized_injective_spec in hc.
    have hinj : injective_on sk (map fst env).
    { eapply injective_on_incl; tea. intros x hx. apply in_or_app. now left. }
    rewrite (sanitize_untyped_env_spec _ _ he) (sanitize_term_spec _ _ ht).
    split.
    - now apply (wf_eprogram_rename sk sn si (env, t)).
    - now apply eval_rename.
  Qed.

  (** * The configuration is renamed by the same function *)

  Lemma sanitize_config_spec c c' :
    sanitize_config f c = Ok c' ->
    c'.(Config.inlinings_opts) = map sk c.(Config.inlinings_opts) /\
    c'.(Config.const_remappings_opts) =
      map (fun x => (sk x.1, x.2)) c.(Config.const_remappings_opts) /\
    c'.(Config.cstr_reorders_opts) =
      map (fun x => (rename_inductive sk x.1, x.2)) c.(Config.cstr_reorders_opts) /\
    c'.(Config.custom_attributes_opts) =
      map (fun x => (sk x.1, x.2)) c.(Config.custom_attributes_opts).
  Proof.
    rewrite /sanitize_config. intros H. inv_bind. cbn.
    repeat split.
    - eapply monad_map_spec_all; tea. apply sanitize_kername_spec.
    - eapply monad_map_spec_all; tea. intros [] y h; cbn in h. inv_bind. now use_specs.
    - eapply monad_map_spec_all; tea. intros [] y h; cbn in h. inv_bind. now use_specs.
    - eapply monad_map_spec_all; tea. intros [] y h; cbn in h. inv_bind. now use_specs.
  Qed.

  (** Membership in a renamed list of names, for a renaming injective on the
      program's and the configuration's names. *)
  Lemma in_sanitized_iff names l kn :
    injective_on sk names -> incl l names -> In kn names ->
    In (sk kn) (map sk l) <-> In kn l.
  Proof.
    intros hinj hl hkn. split.
    - move/in_map_iff => [x [e hx]]. have -> : kn = x by apply hinj; auto.
      exact hx.
    - intros h. now apply in_map.
  Qed.

  (** Lookup by key in a renamed association list. *)
  Lemma find_sanitized {A} names (l : list (kername * A)) kn :
    injective_on sk names -> incl (map fst l) names -> In kn names ->
    find (fun x => eq_kername x.1 (sk kn)) (map (fun x => (sk x.1, x.2)) l) =
    option_map (fun x => (sk x.1, x.2)) (find (fun x => eq_kername x.1 kn) l).
  Proof.
    intros hinj hl hkn. induction l as [|[k a] l IH]; cbn => //.
    change (eq_kername ?a ?b) with (eqb a b).
    case: (eqb_spec k kn) => [->|neq].
    - now rewrite eqb_refl.
    - case: (eqb_spec (sk k) (sk kn)) => [e|_].
      + exfalso. apply neq. apply hinj; auto. apply hl. now left.
      + apply IH. intros x hx. apply hl. now right.
  Qed.

End Spec.

(** * Regression examples *)

Module Examples.
  Import NameSanitize.

  Definition kn_dot : kername := (MPfile ["M"%bs], "a.b"%bs).

  (** Names inside a primitive array literal are sanitized like the others. *)
  Example sanitize_array_literal :
    sanitize_term ocaml_sanitizer
      (tPrim (prim_array {| array_default := tConst kn_dot; array_value := [tConst kn_dot] |})) =
    Ok (tPrim (prim_array {| array_default := tConst (MPfile ["M"%bs], "a_UU2eb"%bs);
                             array_value := [tConst (MPfile ["M"%bs], "a_UU2eb"%bs)] |})).
  Proof. vm_compute. reflexivity. Qed.

  Definition is_err {A} (r : result' A) : bool :=
    match r with Err _ => true | Ok _ => false end.

  (** A NUL byte followed by [00e9] and the character [é] have the same OCaml
      escape [_UU0000e9]; the check rejects the pair. *)
  Example sanitize_collision_rejected :
    is_err (check_sanitized_injective ocaml_sanitizer
      [(MPfile ["M"%bs], String.String Byte.x00 "00e9"%bs); (MPfile ["M"%bs], "é"%bs)]) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** An escaped name and the literal spelling of its escape stay distinct. *)
  Example sanitize_escape_accepted :
    check_sanitized_injective ocaml_sanitizer [kn_dot; (MPfile ["M"%bs], "a_UU2eb"%bs)] = Ok tt.
  Proof. vm_compute. reflexivity. Qed.
End Examples.
