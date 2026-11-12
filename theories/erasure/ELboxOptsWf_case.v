(** * Well-formedness of the [case_id] and [case_fun] rewrites of [ELboxOpts] *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EWellformed EInduction.
From Peregrine Require Import ELboxOpts.
From Stdlib Require Import ssreflect ssrbool.

Import ListNotations.
Local Open Scope bool_scope.

(** ** General helpers on [exchange], [strip_lambdas], [mk_lambdas]
    (shared with the [let_fun] proof; candidates for deduplication) *)
Section LboxOptsWfHelpers.
  Context {efl : EEnvFlags} (Σ : global_declarations).

  Lemma wellformed_exchange m n k j t :
    k + m + n <= j -> wellformed Σ j t -> wellformed Σ j (exchange m n k t).
  Proof.
    induction t in k, j |- * using EInduction.term_forall_list_ind; intros hle wf;
      cbn -[Nat.ltb EGlobalEnv.lookup_constructor_pars_args EGlobalEnv.lookup_constructor
            EGlobalEnv.lookup_inductive EGlobalEnv.lookup_projection EGlobalEnv.lookup_constant] in *;
      rtoProp; intuition auto.
    - apply Nat.ltb_lt in H0.
      destruct (Nat.ltb_spec n0 k); [|destruct (Nat.ltb_spec (n0 - k) m); [|destruct (Nat.ltb_spec (n0 - k) (m + n))]];
        cbn; rewrite H /=; apply Nat.ltb_lt; lia.
    - solve_all.
    - eapply IHt; [|eassumption]; lia.
    - eapply IHt2; [|eassumption]; lia.
    - rewrite length_map. destruct cstr_as_blocks.
      + destruct EGlobalEnv.lookup_constructor_pars_args as [[]|];
        rtoProp; intuition auto; solve_all.
      + now destruct args.
    - now rewrite length_map.
    - solve_all.
    - solve_all; destruct x as [na bd r]; cbn in *. now destruct bd.
    - unfold wf_fix_gen in *; rtoProp; rewrite length_map; intuition auto.
      solve_all. unfold test_def in *; cbn in *. eapply a; [|eassumption]. lia.
    - unfold wf_fix_gen in *; rtoProp; rewrite length_map; intuition auto.
      solve_all. unfold test_def in *; cbn in *. eapply a; [|eassumption]. lia.
    - now rewrite has_prim_map_prim.
    - rewrite test_prim_map.
      eapply primProp_impl_test_prim.
      eapply test_prim_impl_primProp in H0.
      eapply primProp_impl; [exact (primProp_conj X H0)|].
      cbn. intros x [h1 h2]. now eapply h1.
  Qed.

  Lemma length_lambda_names m t :
    m <= count_lambdas t -> #|lambda_names m t| = m.
  Proof.
    induction m in t |- *; [reflexivity|].
    destruct t; cbn; try lia. intros h. f_equal. apply IHm. lia.
  Qed.

  Lemma wellformed_strip_lambdas m j t :
    m <= count_lambdas t -> wellformed Σ j t -> wellformed Σ (m + j) (strip_lambdas m t).
  Proof.
    induction m in j, t |- *; [easy|].
    destruct t; cbn; try lia. intros h wf. rtoProp.
    rewrite -Nat.add_succ_r. apply IHm; [lia|assumption].
  Qed.

  Lemma wellformed_mk_lambdas nas j b :
    has_tLambda -> wellformed Σ (#|nas| + j) b -> wellformed Σ j (mk_lambdas nas b).
  Proof.
    intros hl. induction nas in j |- *; cbn; [easy|].
    intros wf. rewrite hl /=. apply IHnas. now rewrite Nat.add_succ_r.
  Qed.

End LboxOptsWfHelpers.

Lemma fold_left_min_le {A} (f : A -> nat) l acc :
  fold_left (fun acc x => Nat.min acc (f x)) l acc <= acc /\
  forall x, In x l -> fold_left (fun acc x => Nat.min acc (f x)) l acc <= f x.
Proof.
  induction l in acc |- *; cbn; [split; [lia|easy]|].
  destruct (IHl (Nat.min acc (f a))) as [h1 h2]. split; [lia|].
  intros x [<-|hin]; [lia|now apply h2].
Qed.

(** ** Pass 3: [case_id] *)

Lemma wellformed_case_id {efl : EEnvFlags} Σ k t : wellformed Σ k t -> wellformed Σ k (case_id t).
Proof.
  destruct t as [| | | | | | | | | [ind np] d brs | | | | | |]; try easy. cbn [case_id].
  destruct brs; [easy|]. destruct forallb; [|easy].
  cbn -[EGlobalEnv.lookup_inductive]. now rtoProp.
Qed.

(** ** Pass 2: [case_fun] *)

Lemma wellformed_case_fun {efl : EEnvFlags} Σ k t : wellformed Σ k t -> wellformed Σ k (case_fun t).
Proof.
  destruct t as [| | | | | | | | | ci d brs0 | | | | | |]; try easy.
  destruct d as [|x| | | | | | | | | | | | | |]; try easy.
  destruct brs0 as [|br0 brs]; [easy|].
  intros wf. cbn -[EGlobalEnv.lookup_inductive] in wf.
  move: wf => /and4P [hcase /and3P [hbrs hrel hx] hbr0 hbrs'].
  cbn [case_fun].
  set (m := fold_left _ _ _).
  destruct (Nat.eqb_spec m 0) as [|hm].
  { cbn -[EGlobalEnv.lookup_inductive]. now rewrite hcase hbrs hrel hx hbr0 hbrs'. }
  pose proof (fold_left_min_le (fun br : list name × term => count_lambdas br.2) (br0 :: brs) (count_lambdas br0.2)) as [_ hmin].
  fold m in hmin. clearbody m.
  assert (hlam : has_tLambda).
  { assert (m <= count_lambdas br0.2) by (apply hmin; now left).
    destruct br0 as [ctx [] ]; cbn in *; try lia. now rtoProp. }
  apply wellformed_mk_lambdas; [assumption|].
  rewrite length_lambda_names; [apply hmin; now left|].
  cbn -[EGlobalEnv.lookup_inductive].
  rewrite hcase length_map hbrs /=. apply/andP; split.
  - rewrite hrel /=. apply Nat.ltb_lt in hx. apply Nat.ltb_lt. lia.
  - assert (hall : forall br, In br (br0 :: brs) ->
      wellformed Σ (#|br.1| + (m + k)) (exchange m #|br.1| 0 (strip_lambdas m br.2))).
    { intros br hin.
      pose proof (hin' := hin). apply hmin in hin'.
      assert (wfbr : wellformed Σ (#|br.1| + k) br.2).
      { destruct hin as [<-|hin]; [assumption|]. now eapply (proj1 (forallb_forall _ _)) in hbrs'. }
      eapply wellformed_strip_lambdas in wfbr; tea.
      replace (#|br.1| + (m + k)) with (m + (#|br.1| + k)) by lia.
      apply wellformed_exchange; [lia|assumption]. }
    rewrite forallb_map /=. apply/andP; split; [apply hall; now left|].
    apply forallb_forall. intros br hin. apply hall. now right.
Qed.
