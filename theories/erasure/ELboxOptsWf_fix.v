(** * Well-formedness of the [fix_eta] lambda-box rewrite (pass 1 of [ELboxOpts])

    [wellformed_fix_eta]: [fix_eta] preserves [wellformed Σ k], assuming
    [has_tBox] (the pass substitutes boxes for the hoisted lambdas, the
    stripped box-lets and the dropped dead parameters).  [has_tBox] holds for
    the pipeline flags at this stage.  [wellformed] only asks fixpoint bodies to
    be lambdas and well-scoped (it does not look at [rarg]), and
    [drop_fix_params] keeps at least one leading lambda ([k >= 1]) on the
    rewritten body and preserves lambdas of the other bodies. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EWellformed EInduction.
From Peregrine Require Import ELboxOpts.

Import ListNotations.
Local Open Scope bool_scope.

(** ** Generic helpers *)

Lemma mapo_spec {A B} {g : A -> option B} {l l'} (E : map_option_out (map g l) = Some l')
  (P : A -> Type) (p : A -> bool) (q : B -> bool) :
  All P l ->
  (forall x y, P x -> p x -> g x = Some y -> q y) ->
  forallb p l ->
  forallb q l' /\ #|l'| = #|l|.
Proof.
  intros HP Hg. induction HP as [|x l Px HPl IH] in l', E |- *; cbn in *; intros Hp.
  - injection E as <-. auto.
  - apply andb_true_iff in Hp as [Hx Hl].
    destruct (g x) eqn:Ex; [|discriminate].
    destruct (map_option_out (map g l)) eqn:Em; [|discriminate].
    injection E as <-.
    destruct (IH l0 eq_refl Hl) as [Hq Hlen]. cbn.
    rewrite (Hg _ _ Px Hx Ex), Hq. split; [reflexivity|now rewrite Hlen].
Qed.

Lemma All_True {A} (l : list A) : All (fun _ => True) l.
Proof. induction l; constructor; auto. Qed.

Lemma forallb_and_split {A} (p1 p2 : A -> bool) l :
  forallb (fun x => p1 x && p2 x) l = forallb p1 l && forallb p2 l.
Proof.
  induction l; cbn; auto. rewrite IHl.
  destruct (p1 a), (p2 a), (forallb p1 l), (forallb p2 l); reflexivity.
Qed.

Lemma forallb_firstn' {A} (p : A -> bool) k l : forallb p l -> forallb p (firstn k l).
Proof.
  induction l in k |- *; destruct k; cbn; auto.
  intros H; apply andb_true_iff in H as [H1 H2]. now rewrite H1, IHl.
Qed.

Lemma forallb_skipn' {A} (p : A -> bool) k l : forallb p l -> forallb p (skipn k l).
Proof.
  induction l in k |- *; destruct k; cbn; auto.
  intros H; apply andb_true_iff in H as [H1 H2]. now apply IHl.
Qed.

Lemma forallb_combine_snd {A B} (r : B -> bool) (s : list A) l :
  forallb r l -> forallb (fun x => r x.2) (combine s l).
Proof.
  induction l in s |- *; destruct s; cbn; auto.
  intros H; apply andb_true_iff in H as [H1 H2]. now rewrite H1, IHl.
Qed.

Section wf.
Context {efl : EEnvFlags} (Σ : global_declarations).

Lemma wf_mkApps_inv m f args :
  wellformed Σ m (mkApps f args) ->
  wellformed Σ m f /\ forallb (wellformed Σ m) args /\ (args = [] \/ has_tApp).
Proof.
  induction args in f |- *; cbn; intros H.
  - auto.
  - destruct (IHargs _ H) as (Hf & Ha & _). cbn in Hf.
    apply andb_true_iff in Hf as [Hf Ha'].
    apply andb_true_iff in Hf as [Happ Hf'].
    split; [exact Hf'|]. split; [cbn; now rewrite Ha'|]. now right.
Qed.

Lemma wf_mkApps m f args :
  has_tApp -> wellformed Σ m f -> forallb (wellformed Σ m) args ->
  wellformed Σ m (mkApps f args).
Proof.
  intros Happ. induction args in f |- *; cbn; intros Hf Ha; auto.
  apply andb_true_iff in Ha as [Ha1 Ha2].
  apply IHargs; auto. cbn. now rewrite Happ, Hf, Ha1.
Qed.

Lemma wf_repeat_box m x : has_tBox -> forallb (wellformed Σ m) (repeat tBox x).
Proof. intros Hb. induction x; cbn; auto. Qed.

Lemma wf_strip_lambdas n b K :
  wellformed Σ K b -> wellformed Σ (Nat.min n (count_lambdas b) + K) (strip_lambdas n b).
Proof.
  induction n in b, K |- *; cbn; intros H; auto.
  destruct b; cbn; auto.
  cbn in H. apply andb_true_iff in H as [_ H].
  specialize (IHn _ _ H). now rewrite <- plus_n_Sm in IHn.
Qed.

Lemma length_lambda_names_min k b : #|lambda_names k b| = Nat.min k (count_lambdas b).
Proof.
  induction k in b |- *; cbn; auto.
  destruct b; cbn; try reflexivity. now rewrite IHk.
Qed.

Lemma wf_mk_lambdas nas b K :
  has_tLambda -> wellformed Σ (#|nas| + K) b -> wellformed Σ K (mk_lambdas nas b).
Proof.
  intros Hl. induction nas in K |- *; cbn; intros H; auto.
  rewrite Hl. apply IHnas. now rewrite <- plus_n_Sm.
Qed.

Lemma isLambda_mk_lambdas nas b : nas <> [] -> isLambda (mk_lambdas nas b).
Proof. destruct nas; cbn; auto. congruence. Qed.

Lemma lambda_names_nonnil k b : k <> 0 -> isLambda b -> lambda_names k b <> [].
Proof. destruct k, b; cbn; congruence. Qed.

Lemma wf_strip_box_lets t j b K :
  strip_box_lets t = (j, b) -> wellformed Σ K t -> wellformed Σ (j + K) b.
Proof.
  revert j b K; induction t; intros j b K Heq H; cbn in Heq;
    try (injection Heq as <- <-; exact H).
  destruct t1; try (injection Heq as <- <-; exact H).
  destruct (strip_box_lets t2) as [j' b'] eqn:E.
  injection Heq as <- <-.
  cbn in H. apply andb_true_iff in H as [_ H].
  specialize (IHt2 _ _ _ eq_refl H). cbn. now rewrite plus_n_Sm.
Qed.

(** ** [drop_aux] *)

Lemma isLambda_drop_aux f k n t t' :
  isLambda t -> drop_aux f k n [] t = Some t' -> isLambda t'.
Proof.
  destruct t; try discriminate. cbn.
  destruct drop_aux; [|discriminate]. intros _ [= <-]. reflexivity.
Qed.

Lemma wf_drop_aux kd nd t :
  forall f acc t' lv, has_tApp ->
  drop_aux f kd nd acc t = Some t' ->
  wellformed Σ lv t -> forallb (wellformed Σ lv) acc ->
  wellformed Σ lv t'.
Proof.
  induction t using term_forall_list_ind;
    intros f acc t' lv Happ Hd Ht Hacc; cbn in Hd.
  all: try solve [injection Hd as <-; now apply wf_mkApps].
  - (* tRel *)
    destruct (Nat.eqb n f).
    + destruct (Nat.leb nd #|acc|); [|discriminate].
      injection Hd as <-. apply wf_mkApps; auto.
      rewrite forallb_app, forallb_firstn', forallb_skipn'; auto.
    + injection Hd as <-. now apply wf_mkApps.
  - (* tEvar *)
    destruct (map_option_out _) as [ts'|] eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [He Ht]. rewrite He. cbn.
    destruct (mapo_spec E _ (wellformed Σ lv) (wellformed Σ lv) X) as [Hq _];
      [|exact Ht|exact Hq].
    intros x y IH Hx Hy. eapply IH; [exact Happ|exact Hy|exact Hx|reflexivity].
  - (* tLambda *)
    destruct (drop_aux (S f) kd nd [] t) eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Hl Ht]. rewrite Hl. cbn.
    eapply IHt; [exact Happ|exact E|exact Ht|reflexivity].
  - (* tLetIn *)
    destruct (drop_aux f kd nd [] t1) eqn:E1; [|discriminate].
    destruct (drop_aux (S f) kd nd [] t2) eqn:E2; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Ht Ht2].
    apply andb_true_iff in Ht as [Hl Ht1]. rewrite Hl. cbn.
    erewrite IHt1, IHt2; [reflexivity|exact Happ|exact E2|exact Ht2|reflexivity|exact Happ|exact E1|exact Ht1|reflexivity].
  - (* tApp *)
    destruct (drop_aux f kd nd [] t2) eqn:E2; [|discriminate].
    cbn in Ht. apply andb_true_iff in Ht as [Ht Ht2].
    apply andb_true_iff in Ht as [_ Ht1].
    eapply IHt1; [exact Happ|exact Hd|exact Ht1|]. cbn. rewrite Hacc, andb_true_r.
    eapply IHt2; [exact Happ|exact E2|exact Ht2|reflexivity].
  - (* tConstruct *)
    destruct (map_option_out _) as [cargs'|] eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. revert Ht. destruct cstr_as_blocks; intros Ht.
    + apply andb_true_iff in Ht as [Ht1 Ht2]. apply andb_true_iff in Ht2 as [Ht2 Ht3].
      destruct (mapo_spec E _ (wellformed Σ lv) (wellformed Σ lv) X) as [Hq Hlen];
        [|exact Ht3|].
      { intros x y IH Hx Hy. eapply IH; [exact Happ|exact Hy|exact Hx|reflexivity]. }
      rewrite Ht1, Hlen, Hq, andb_true_r. exact Ht2.
    + destruct args; [|apply andb_true_iff in Ht as [_ Ht]; discriminate].
      cbn in E. injection E as <-. exact Ht.
  - (* tCase *)
    destruct (drop_aux f kd nd [] t) eqn:E1; [|discriminate].
    destruct (map_option_out _) as [brs'|] eqn:E2; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Hc Ht]. apply andb_true_iff in Ht as [Ht Hbrs].
    apply andb_true_iff in Ht as [Hwb Htt].
    destruct (mapo_spec E2 _ (fun br => wellformed Σ (#|br.1| + lv) br.2) (fun br => wellformed Σ (#|br.1| + lv) br.2) X)
      as [Hq Hlen]; [|exact Hbrs|].
    { intros [nas b] y IH Hx Hy. cbn in *.
      destruct (drop_aux _ kd nd [] b) eqn:Eb; [|discriminate]. injection Hy as <-. cbn.
      eapply IH; [exact Happ|exact Eb|exact Hx|reflexivity]. }
    rewrite Hc, Hlen, Hwb, Hq, andb_true_r. cbn.
    eapply IHt; [exact Happ|exact E1|exact Htt|reflexivity].
  - (* tProj *)
    destruct (drop_aux f kd nd [] t) eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Hl Ht]. rewrite Hl. cbn.
    eapply IHt; [exact Happ|exact E|exact Ht|reflexivity].
  - (* tFix *)
    destruct (map_option_out _) as [mfix'|] eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. unfold wf_fix_gen in *.
    apply andb_true_iff in Ht as [Ht Hw]. apply andb_true_iff in Ht as [Hf Hl].
    apply andb_true_iff in Hw as [Hidx Hb].
    destruct (mapo_spec E _ (fun d => isLambda (dbody d) && wellformed Σ (#|m| + lv) (dbody d))
                (fun d => isLambda (dbody d) && wellformed Σ (#|m| + lv) (dbody d)) X)
      as [Hq Hlen]; [| |].
    { intros [na b r] y IH Hx Hy. cbn in *.
      destruct (drop_aux _ kd nd [] b) eqn:Eb; [|discriminate]. injection Hy as <-. cbn.
      apply andb_true_iff in Hx as [Hx1 Hx2].
      rewrite (isLambda_drop_aux _ _ _ _ _ Hx1 Eb). cbn.
      eapply IH; [exact Happ|exact Eb|exact Hx2|reflexivity]. }
    { rewrite forallb_and_split. apply andb_true_iff; split; assumption. }
    rewrite forallb_and_split in Hq. apply andb_true_iff in Hq as [Hq1 Hq2].
    rewrite Hlen. apply andb_true_iff; split; [apply andb_true_iff; split; assumption|].
    apply andb_true_iff; split; assumption.
  - (* tCoFix *)
    destruct (map_option_out _) as [mfix'|] eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. unfold wf_fix_gen in *.
    apply andb_true_iff in Ht as [Hf Hw]. apply andb_true_iff in Hw as [Hidx Hb].
    destruct (mapo_spec E _ (fun d => wellformed Σ (#|m| + lv) (dbody d))
                (fun d => wellformed Σ (#|m| + lv) (dbody d)) X)
      as [Hq Hlen]; [|exact Hb|].
    { intros [na b r] y IH Hx Hy. cbn in *.
      destruct (drop_aux _ kd nd [] b) eqn:Eb; [|discriminate]. injection Hy as <-. cbn.
      eapply IH; [exact Happ|exact Eb|exact Hx|reflexivity]. }
    rewrite Hlen. apply andb_true_iff; split; [assumption|].
    apply andb_true_iff; split; assumption.
  - (* tPrim *)
    destruct (occurs_rel f (tPrim p)); [discriminate|].
    injection Hd as <-. now apply wf_mkApps.
  - (* tLazy *)
    destruct (drop_aux f kd nd [] t) eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Hl Ht]. rewrite Hl. cbn.
    eapply IHt; [exact Happ|exact E|exact Ht|reflexivity].
  - (* tForce *)
    destruct (drop_aux f kd nd [] t) eqn:E; [|discriminate].
    injection Hd as <-. apply wf_mkApps; auto.
    cbn in Ht |- *. apply andb_true_iff in Ht as [Hl Ht]. rewrite Hl. cbn.
    eapply IHt; [exact Happ|exact E|exact Ht|reflexivity].
Qed.


(** ** [drop_fix_params] *)

Lemma wf_drop_fix_params kd nd t t' lv :
  has_tApp -> has_tLambda -> has_tBox -> kd <> 0 ->
  drop_fix_params kd nd t = Some t' -> wellformed Σ lv t -> wellformed Σ lv t'.
Proof.
  intros Happ Hlam Hbox Hk Hd Ht.
  destruct t; try discriminate. cbn in Hd.
  destruct (map_option_out _) as [mfix'|] eqn:E; [|discriminate].
  injection Hd as <-.
  cbn in Ht |- *. unfold wf_fix_gen in *.
  apply andb_true_iff in Ht as [Ht Hw]. apply andb_true_iff in Ht as [Hf Hl].
  apply andb_true_iff in Hw as [Hidx Hb].
  set (r := fun d : def term => isLambda (dbody d) && wellformed Σ (#|mfix| + lv) (dbody d)).
  destruct (mapo_spec E (fun _ => True) (fun x => r x.2) r (All_True _)) as [Hq Hlen]; [| |].
  - intros [i [na b ra]] y _ Hx Hy. unfold r in Hx. cbn in Hx, Hy.
    apply andb_true_iff in Hx as [Hx1 Hx2].
    destruct (drop_aux _ kd nd [] b) as [b'|] eqn:Eb; [|discriminate].
    pose proof (isLambda_drop_aux _ _ _ _ _ Hx1 Eb) as Hlb.
    pose proof (wf_drop_aux _ _ _ _ _ _ _ Happ Eb Hx2 eq_refl) as Hwb.
    destruct (Nat.eqb i idx); injection Hy as <-; unfold r; cbn.
    + rewrite isLambda_mk_lambdas by (apply lambda_names_nonnil; auto). cbn.
      apply wf_mk_lambdas; auto. rewrite length_lambda_names_min.
      eapply wellformed_subst; [apply wf_repeat_box; exact Hbox|].
      rewrite repeat_length.
      eapply wellformed_up; [apply wf_strip_lambdas; exact Hwb|].
      destruct (Nat.min_spec nd (count_lambdas b')) as [[? ->]|[? ->]];
      destruct (Nat.min_spec kd (count_lambdas b')) as [[? ->]|[? ->]]; lia.
    + rewrite Hlb, Hwb. reflexivity.
  - apply forallb_combine_snd. unfold r. rewrite forallb_and_split.
    apply andb_true_iff; split; assumption.
  - unfold r in Hq. rewrite forallb_and_split in Hq. apply andb_true_iff in Hq as [Hq1 Hq2].
    rewrite length_combine, length_seq, Nat.min_id in Hlen.
    rewrite Hlen. apply andb_true_iff; split; [apply andb_true_iff; split; assumption|].
    apply andb_true_iff; split; assumption.
Qed.

End wf.

(** ** Main lemma *)

Lemma wellformed_fix_eta {efl : EEnvFlags} Σ k t :
  has_tBox -> wellformed Σ k t -> wellformed Σ k (fix_eta t).
Proof.
  intros Hbox H. unfold fix_eta.
  destruct (Nat.eqb (count_lambdas t) 0) eqn:Ek; [exact H|].
  assert (Hlam : has_tLambda).
  { destruct t; try discriminate. cbn in H. now apply andb_true_iff in H as [? _]. }
  pose proof (wf_strip_lambdas Σ (count_lambdas t) t k H) as H1. rewrite Nat.min_id in H1.
  destruct (strip_box_lets (strip_lambdas (count_lambdas t) t)) as [j body] eqn:Es.
  pose proof (wf_strip_box_lets Σ _ _ _ _ Es H1) as H2.
  destruct (decompose_app body) as [hd args] eqn:Ed.
  apply decompose_app_inv in Ed. subst body.
  destruct (wf_mkApps_inv Σ _ _ _ H2) as (Hhd & _ & Happ).
  destruct hd; try exact H.
  destruct (nofree_range _ _ _ && fix_eta_args_ok _ _ _ _ _) eqn:Hc; [|exact H].
  assert (Hsub : wellformed Σ k (subst0 (repeat tBox (count_lambdas t + j)) (tFix mfix idx))).
  { eapply wellformed_subst; [apply wf_repeat_box; exact Hbox|]. rewrite repeat_length.
    replace (count_lambdas t + j + k) with (j + (count_lambdas t + k)) by lia. exact Hhd. }
  destruct (#|args| =? count_lambdas t) eqn:En; [exact Hsub|].
  destruct (drop_fix_params _ _ _) eqn:Ed; [|exact H].
  eapply wf_drop_fix_params; [| exact Hlam | exact Hbox | | exact Ed | exact Hsub].
  - destruct Happ as [->|]; [|assumption].
    apply andb_true_iff in Hc as [_ Hc]. unfold fix_eta_args_ok in Hc.
    apply andb_true_iff in Hc as [Hc _]. cbn in Hc. apply Nat.leb_le in Hc.
    apply Nat.eqb_neq in Ek. lia.
  - now apply Nat.eqb_neq.
Qed.

