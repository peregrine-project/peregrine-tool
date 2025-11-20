From Coq Require Import List.
From Coq Require Import Logic.Decidable.
From Coq Require Import ssreflect.
From MetaCoq.Utils Require Import ReflectEq.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Common Require Import EnvMap.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import EWellformed.
From MetaCoq.Erasure.Typed Require ExAst.
From Equations Require Import Equations.

Import ListNotations.
Import EnvMap.



Definition agda_eflags : EEnvFlags :=
  {| has_axioms      := true;
     term_switches   :=
       {| has_tBox        := true
        ; has_tRel        := true
        ; has_tVar        := true
        ; has_tEvar       := true
        ; has_tLambda     := true
        ; has_tLetIn      := true
        ; has_tApp        := true
        ; has_tConst      := true
        ; has_tConstruct  := true
        ; has_tCase       := true
        ; has_tProj       := false (* Our backends shouldn't produce projections *)
        ; has_tFix        := true
        ; has_tCoFix      := true
        ; has_tPrim       := all_primitive_flags
        ; has_tLazy_Force := true
        |};
     has_cstr_params := false;  (* Agda already drops constructor params *)
     cstr_as_blocks  := true;   (* The backend fully applies ctors       *)
  |}.

Definition agda_typed_eflags : EEnvFlags :=
  {| has_axioms      := true;
     term_switches   :=
       {| has_tBox        := true
        ; has_tRel        := true
        ; has_tVar        := true
        ; has_tEvar       := true
        ; has_tLambda     := true
        ; has_tLetIn      := true
        ; has_tApp        := true
        ; has_tConst      := true
        ; has_tConstruct  := true
        ; has_tCase       := true
        ; has_tProj       := false (* Our backends shouldn't produce projections *)
        ; has_tFix        := true
        ; has_tCoFix      := true
        ; has_tPrim       := all_primitive_flags
        ; has_tLazy_Force := true
        |};
     has_cstr_params := false;  (* Agda already drops constructor params *)
     cstr_as_blocks  := false;
  |}.

From MetaCoq.Erasure Require Import EGlobalEnv.
From MetaCoq.Erasure Require Import EPrimitive.

From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure.Typed Require Import ResultMonad.

Import MCMonadNotation.

From MetaCoq.Common Require Import Primitive.


Section Wf.

  Definition assert (b : bool) (s : unit -> string) : (fun T => result T string) unit :=
    if b then Ok tt else Err (s tt).

  Definition assert_some {A : Type} (b : option A) (s : unit -> string) : (fun T => result T string) unit :=
    match b with
    | Some _ =>  Ok tt
    | None => Err (s tt)
    end.

  Definition result_forall {A : Type} (f : A -> (fun T => result T string) unit ) (l : list A) :=
    List.fold_left (fun a t => a ;; f t) l (Ok tt).

  Definition wf_fix_gen_ (wf : nat -> term -> (fun T => result T string) unit) k mfix idx :=
    let k' := List.length mfix + k in
    assert (idx <? #|mfix|) (fun _ => "Fixpoint index out of bounds") ;;
    result_forall (fun d => (wf k') d.(dbody)) mfix.

  Definition bool_of_result {T E : Type} (r : result T E) : bool :=
    match r with
    | Ok _ => true
    | Err _ => false
    end.

  Definition has_prim_ {epfl : EPrimitiveFlags} (p : prim_val term) : (fun T => result T string) unit :=
    match prim_val_tag p with
    | primInt => assert has_primint (fun _ => "Program contains primitive integers")
    | primFloat => assert has_primfloat (fun _ => "Program contains primitive floats")
    | primString => assert has_primstring (fun _ => "Program contains primitive strings")
    | primArray => assert has_primarray (fun _ => "Program contains primitive arrays")
    end.

  Fixpoint wellformed {efl  : EEnvFlags} Σ (k : nat) (t : term) {struct t} : (fun T => result T string) unit :=
    match t with
    | tRel i => assert has_tRel (fun _ => "Program contains tRel") ;; assert (Nat.ltb i k) (fun _ => "Program not closed, invalid tRel " ^ (string_of_nat i))
    | tEvar ev args => assert has_tEvar (fun _ => "Program contains tEvar") ;; result_forall (wellformed Σ k) args
    | tLambda _ M => assert has_tLambda (fun _ => "Program contains tLambda") ;; wellformed Σ (S k) M
    | tApp u v =>
      assert has_tApp (fun _ => "Program contains tApp") ;;
      wellformed Σ k u ;;
      wellformed Σ k v
    | tLetIn na b b' =>
      assert has_tLetIn (fun _ => "Program contains tLetIn") ;;
      wellformed Σ k b ;;
      wellformed Σ (S k) b'
    | tCase ind c brs =>
      assert has_tCase (fun _ => "Program contains tCase") ;;
      let brs' := result_forall (fun br => wellformed Σ (#|br.1| + k) br.2) brs in
      assert (wf_brs Σ ind.1 #|brs|) (fun _ => "Case not exhaustive") ;;
      wellformed Σ k c ;;
      brs'
    | tProj p c =>
      assert has_tProj (fun _ => "Program contains tProj") ;;
      assert_some (lookup_projection Σ p) (fun _ => "Projection " ^ (string_of_inductive p.(proj_ind))^":"^(string_of_nat p.(proj_npars))^","^(string_of_nat p.(proj_arg)) ^ " not found") ;;
      wellformed Σ k c
    | tFix mfix idx =>
      assert has_tFix (fun _ => "Program contains tFix") ;;
      result_forall (fun t => assert ((isLambda ∘ dbody) t) (fun _ => "Fixpoint body is not a lambda")) mfix ;;
      wf_fix_gen_ (wellformed Σ) k mfix idx
    | tCoFix mfix idx =>
      assert has_tCoFix (fun _ => "Program contains tCoFix") ;;
      wf_fix_gen_ (wellformed Σ) k mfix idx
    | tBox => assert has_tBox (fun _ => "Program contains tBox")
    | tConst kn =>
      assert has_tConst (fun _ => "Program contains tConst") ;;
      match lookup_constant Σ kn with
      | Some d => assert (has_axioms || isSome d.(cst_body)) (fun _ => "Invalid axiom " ^ (string_of_kername kn))
      | _ => Err ("Constant not found in environment " ^ (string_of_kername kn))
      end
    | tConstruct ind c block_args =>
      assert has_tConstruct (fun _ => "Program contains tConstruct") ;;
      assert_some (lookup_constructor Σ ind c) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not found") ;;
      if cstr_as_blocks then
        match lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => assert ((p + a) == #|block_args|) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not fully applied")
        | _ => Ok tt end
        ;; result_forall (wellformed Σ k) block_args
      else assert (is_nil block_args) (fun _ => "Constructor args non-empty")
    | tVar _ => assert has_tVar (fun _ => "Program contains tVar")
    | tPrim p => has_prim_ p ;; assert (test_prim (fun t => bool_of_result (wellformed Σ k t)) p) (fun _ => "Invalid array primitive")
    | tLazy t => assert has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed Σ k t
    | tForce t => assert has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed Σ k t
    end.

  Definition wf_projections idecl : (fun T => result T string) unit :=
    match idecl.(ind_projs) with
    | [] => Ok tt
    | _ =>
      match idecl.(ind_ctors) with
      | [cstr] => assert (#|idecl.(ind_projs)| == cstr.(cstr_nargs)) (fun _ => "Number of primitive projections doesn't match constructor args")
      | _ => Err "Invalid projection"
      end
    end.

  Definition wf_inductive (idecl : one_inductive_body) : (fun T => result T string) unit :=
    wf_projections idecl.

  Definition wf_minductive {efl  : EEnvFlags} (mdecl : mutual_inductive_body) : (fun T => result T string) unit :=
    assert (has_cstr_params || (mdecl.(ind_npars) == 0)) (fun _ => "Has constructor params") ;;
    result_forall wf_inductive mdecl.(ind_bodies).

  Definition wf_global_decl {efl  : EEnvFlags} Σ d : (fun T => result T string) unit :=
    match d with
    | ConstantDecl cb =>
      match cb.(cst_body) with
      | None => assert has_axioms (fun _ => "Program contains axioms")
      | Some cb => wellformed Σ 0 cb
      end
    | InductiveDecl idecl => wf_minductive idecl
    end.

  Fixpoint check_fresh_global (k : kername) (decls : global_declarations) : (fun T => result T string) unit :=
    match decls with
    | []    => Ok tt
    | p::ds =>
      assert (negb (eq_kername (fst p) k)) (fun _ => "Duplicate definition " ^ (string_of_kername (fst p))) ;;
      check_fresh_global k ds
    end.

  Fixpoint check_wf_glob {efl : EEnvFlags} (decls : global_declarations) : (fun T => result T string) unit :=
    match decls with
    | []    => Ok tt
    | p::ds =>
      check_wf_glob ds ;;
      check_fresh_global (fst p) ds ;;
      map_error (fun e => "Error while checking " ^ (string_of_kername (fst p)) ^ ": " ^ e) (wf_global_decl ds (snd p))
    end.

  Definition check_wf_program {efl : EEnvFlags} (p : program) : (fun T => result T string) unit :=
    check_wf_glob (fst p) ;; wellformed (fst p) 0 (snd p).

End Wf.

Section WfCorrect.
  Fixpoint check_fresh_global_b (k : kername) (decls : global_declarations) : bool :=
    match decls with
    | []    => true
    | p::ds => negb (eq_kername (fst p) k) && check_fresh_global_b k ds
    end.

  Fixpoint check_wf_glob_b {efl : EEnvFlags} (decls : global_declarations) : bool :=
    match decls with
    | []    => true
    | p::ds => check_wf_glob_b ds && check_fresh_global_b (fst p) ds && EWellformed.wf_global_decl ds (snd p)
    end.

  Definition check_wf_program_b {efl : EEnvFlags} (p : program) : bool :=
    check_wf_glob_b (fst p) && EWellformed.wellformed (fst p) 0 (snd p).

  Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

  (* freshness boolean check coincides with the freshness property *)
  Fixpoint check_fresh_globalbP (k : kername) (decls : global_declarations)
    : reflectProp (fresh_global k decls) (check_fresh_global_b k decls).
  Proof.
    dependent elimination decls; simpl.
    - apply reflectP.
      apply Forall_nil.
    - destruct (inspect (fst p == k)).
      destruct x; rewrite e; simpl.
      + apply reflectF => global_ds.
        dependent elimination global_ds.
        apply n.
        by apply eqb_eq.
      + destruct (check_fresh_globalbP k l).
        * apply reflectP.
          apply Forall_cons; auto.
          destruct (neqb (fst p) k) as [Hneq _].
          apply Hneq.
          by rewrite e.
        * apply reflectF => gds.
          by dependent elimination gds.
  Qed.

  (* well-formedness boolean check coincides with the wf property *)
  Fixpoint check_wf_globbP {efl : EEnvFlags} (decls : global_declarations)
    : reflectProp (wf_glob decls) (check_wf_glob_b decls).
  Proof.
    dependent elimination decls.
    - apply reflectP.
      apply wf_glob_nil.
    - remember (check_wf_glob_b l).
      pose x := (check_wf_globbP efl l).
      rewrite <-Heqb in x.
      destruct x; simpl; rewrite <-Heqb; simpl.
      + remember (check_fresh_global_b (fst p) l).
        pose x := (check_fresh_globalbP (fst p) l).
        rewrite <-Heqb0 in x.
        destruct x => /=.
        remember (EWellformed.wf_global_decl l (snd p)).
        destruct b.
        apply reflectP.
        destruct p.
        by constructor.
        apply reflectF => gds.
        dependent elimination gds.
        simpl in Heqb1.
        rewrite <-Heqb1 in i.
        discriminate i.
        apply reflectF => gds.
        by dependent elimination gds.
      + apply reflectF => gds.
        by dependent elimination gds.
  Qed.



  Lemma result_mapb {E1 E2 T : Type} : forall (f : E1 -> E2) (r : result T E1),
    bool_of_result (map_error f r) = bool_of_result r.
  Proof.
    intros.
    destruct r; reflexivity.
  Qed.

  Lemma result_assertb' : forall b s,
    bool_of_result (assert b s) = b.
  Proof.
    intros.
    destruct b; reflexivity.
  Qed.

  Lemma result_assertb : forall b s (c : result unit string),
    bool_of_result (assert b s ;; c) = b && (bool_of_result c).
  Proof.
    intros.
    destruct b; reflexivity.
  Qed.

  Lemma result_assert_someb' {A : Type} : forall (o : option A) s,
    bool_of_result (assert_some o s) = isSome o.
  Proof.
    intros.
    destruct o; reflexivity.
  Qed.

  Lemma result_assert_someb {A : Type} : forall (o : option A) s (c : result unit string),
    bool_of_result (assert_some o s ;; c) = isSome o && (bool_of_result c).
  Proof.
    intros.
    destruct o; reflexivity.
  Qed.

  Lemma result_bindb {T E: Type} : forall (c1 c2 : (fun T => result T E) T),
    bool_of_result (c1 ;; c2) = bool_of_result c1 && bool_of_result c2.
  Proof.
    intros.
    destruct c1, c2; reflexivity.
  Qed.

  Lemma result_forallb' {A : Type} : forall (f : A -> (fun T => result T string) unit)  h (t : list A),
    bool_of_result (fold_left (fun a t => a ;; f t) (h :: t) (Ok tt)) =
    bool_of_result (f h) && bool_of_result (fold_left (fun a t => a ;; f t) t (Ok tt)).
  Proof.
    intros.
    cbn.
    destruct (f h); simpl.
    - destruct t1.
      reflexivity.
    - induction t0.
      + reflexivity.
      + cbn.
        apply IHt0.
  Qed.

  Lemma result_forallb {A : Type} : forall f f' (l : list A),
    (forall x, bool_of_result (f x) = f' x) ->
    bool_of_result (result_forall f l) = forallb f' l.
  Proof.
    induction l; auto.
    intros.
    unfold result_forall.
    simpl.
    rewrite result_forallb'.
    rewrite H.
    rewrite IHl.
    assumption.
    reflexivity.
  Qed.

  Lemma result_forall_allb {A : Type} : forall f f' (l : list A),
    All (fun x => bool_of_result (f x) = f' x) l ->
    bool_of_result (result_forall f l) = forallb f' l.
  Proof.
    induction l; auto.
    intros.
    unfold result_forall.
    simpl.
    rewrite result_forallb'.
    inversion X; subst.
    rewrite H0.
    rewrite IHl.
    assumption.
    reflexivity.
  Qed.



  Theorem wf_fix_gen_equiv {efl  : EEnvFlags} : forall Σ k m n,
    All
      (fun x : def term =>
      bool_of_result (wellformed Σ (#|m| + k) (dbody x)) =
      test_def (EWellformed.wellformed Σ (#|m| + k)) x) m ->
    bool_of_result (wf_fix_gen_ (wellformed Σ) k m n) = wf_fix Σ k m n.
  Proof.
    intros.
    unfold wf_fix_gen_, wf_fix_gen.
    rewrite result_assertb.
    apply ssrbool.andb_id2l => _.
    apply result_forall_allb.
    assumption.
  Qed.

  Theorem has_prim_equiv {efl  : EEnvFlags} : forall p,
    bool_of_result (has_prim_ p) = has_prim p.
  Proof.
    intros.
    unfold has_prim_, has_prim.
    destruct p; simpl.
    destruct x; simpl.
    + rewrite result_assertb'.
      reflexivity.
    + rewrite result_assertb'.
      reflexivity.
    + rewrite result_assertb'.
      reflexivity.
    + rewrite result_assertb'.
      reflexivity.
  Qed.

  Theorem wellformed_equiv {efl  : EEnvFlags} : forall t Σ k,
    bool_of_result (wellformed Σ k t) = EWellformed.wellformed Σ k t.
  Proof.
    (* induction t0. *)
    induction t0 using EInduction.term_forall_list_ind; intros.
    - (* tBox *)
      simpl.
      rewrite result_assertb'.
      reflexivity.
    - (* tRel *)
      simpl.
      rewrite result_assertb.
      rewrite result_assertb'.
      reflexivity.
    - (* tVar *)
      simpl.
      rewrite result_assertb'.
      reflexivity.
    - (* tEvar *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      apply result_forall_allb.
      eapply make_All_All.
      2 : apply X.
      auto.
    - (* tLambda *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      apply IHt0.
    - (* tletIn *)
      simpl.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_bindb.
      rewrite IHt0_1 IHt0_2.
      reflexivity.
    - (* tApp *)
      simpl.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_bindb.
      rewrite IHt0_1 IHt0_2.
      reflexivity.
    - (* tConst *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      destruct lookup_constant; auto.
      rewrite result_assertb'.
      reflexivity.
    - (* tConstruct *)
      simpl.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_assert_someb.
      apply ssrbool.andb_id2l => _.
      destruct cstr_as_blocks.
      + destruct lookup_constructor_pars_args.
        * destruct p.
          rewrite result_assertb.
          apply ssrbool.andb_id2l => _.
          apply result_forall_allb.
          eapply make_All_All.
          2 : apply X.
          auto.
        * simpl.
          apply result_forall_allb.
          eapply make_All_All.
          2 : apply X.
          auto.
      + rewrite result_assertb'.
        reflexivity.
    - (* tCase *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_bindb.
      rewrite IHt0.
      apply ssrbool.andb_id2l => _.
      apply result_forall_allb.
      eapply make_All_All.
      2 : apply X.
      auto.
    - (* tProj *)
      simpl.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_assert_someb.
      apply ssrbool.andb_id2l => _.
      apply IHt0.
    - (* tFix *)
      simpl.
      rewrite result_assertb.
      rewrite <- andb_assoc.
      apply ssrbool.andb_id2l => _.
      rewrite result_bindb.
      f_equal.
      apply result_forall_allb.
      eapply make_All_All.
      2 : apply X.
      intros.
      rewrite result_assertb'.
      reflexivity.
      apply wf_fix_gen_equiv.
      eapply make_All_All.
      2 : apply X.
      auto.
    - (* tCoFix *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      apply wf_fix_gen_equiv.
      eapply make_All_All.
      2 : apply X.
      auto.
    - (* tPrim *)
      simpl.
      rewrite result_bindb.
      rewrite has_prim_equiv.
      apply ssrbool.andb_id2l => _.
      rewrite result_assertb'.
      inversion X; subst.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + cbn.
        destruct X0.
        unfold test_array_model.
        rewrite e.
        apply ssrbool.andb_id2l => _.
        eapply All_forallb_eq_forallb.
        apply a0.
        auto.
    - (* tLazy *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      rewrite IHt0.
      reflexivity.
    - (* tForce *)
      simpl.
      rewrite result_assertb.
      apply ssrbool.andb_id2l => _.
      rewrite IHt0.
      reflexivity.
  Qed.

  Theorem wf_projections_equiv : forall oib,
    bool_of_result (wf_projections oib) = EWellformed.wf_projections oib.
  Proof.
    intros.
    unfold wf_projections, EWellformed.wf_projections.
    destruct oib; simpl.
    destruct ind_projs; simpl; auto.
    destruct ind_ctors; simpl; auto.
    destruct ind_ctors; simpl; auto.
    rewrite result_assertb'.
    reflexivity.
  Qed.

  Theorem wf_inductive_equiv : forall oib,
    bool_of_result (wf_inductive oib) = EWellformed.wf_inductive oib.
  Proof.
    intros.
    apply wf_projections_equiv.
  Qed.

  Theorem wf_minductive_equiv {efl  : EEnvFlags}  : forall m,
    bool_of_result (wf_minductive m) = EWellformed.wf_minductive m.
  Proof.
    intros.
    rewrite result_assertb.
    apply ssrbool.andb_id2l => _.
    apply result_forallb.
    apply wf_inductive_equiv.
  Qed.

  Theorem wf_global_decl_equiv {efl  : EEnvFlags} : forall Σ d,
    bool_of_result (wf_global_decl Σ d) = EWellformed.wf_global_decl Σ d.
  Proof.
    intros.
    destruct d; simpl.
    - destruct cst_body; simpl.
      + by rewrite wellformed_equiv.
      + by rewrite result_assertb'.
    - apply wf_minductive_equiv.
  Qed.

  Theorem check_fresh_global_equiv : forall k d,
    bool_of_result (check_fresh_global k d) = check_fresh_global_b k d.
  Proof.
    induction d; auto; simpl.
    rewrite result_assertb.
    apply ssrbool.andb_id2l => //.
  Qed.

  Theorem check_wf_glob_equiv {efl : EEnvFlags} : forall d,
    bool_of_result (check_wf_glob d) = check_wf_glob_b d.
  Proof.
    induction d; auto; simpl.
    rewrite 2!result_bindb.
    rewrite result_mapb.
    rewrite IHd.
    rewrite check_fresh_global_equiv.
    rewrite wf_global_decl_equiv.
    rewrite <- andb_assoc.
    reflexivity.
  Qed.

  Theorem check_wf_program_equiv {efl : EEnvFlags} : forall p,
    bool_of_result (check_wf_program p) = check_wf_program_b p.
  Proof.
    intros.
    unfold check_wf_program_b; cbn.
    rewrite <- check_wf_glob_equiv.
    destruct check_wf_glob; auto.
    rewrite andb_true_l.
    apply wellformed_equiv.
  Qed.

  Lemma check_fresh_globalP (k : kername) (decls : global_declarations)
    : reflectProp (fresh_global k decls) (bool_of_result (check_fresh_global k decls)).
  Proof.
    rewrite check_fresh_global_equiv.
    apply check_fresh_globalbP.
  Qed.

  Lemma check_wf_globP {efl : EEnvFlags} (decls : global_declarations)
    : reflectProp (wf_glob decls) (bool_of_result (check_wf_glob decls)).
  Proof.
    rewrite check_wf_glob_equiv.
    apply check_wf_globbP.
  Qed.

End WfCorrect.



Module CheckWfExAst.
  Import ExAst.

  Definition check_wf_typed_program {efl : EEnvFlags} (p : global_env) : (fun T => result T string) unit  :=
    check_wf_glob (trans_env p).

End CheckWfExAst.
