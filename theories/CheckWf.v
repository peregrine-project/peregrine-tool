From Stdlib Require Import List.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import ReflectEq.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import EnvMap.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure Require Import EWellformed.
From MetaRocq.Erasure.Typed Require ExAst.
From MetaRocq.Erasure Require Import EGlobalEnv.
From MetaRocq.Erasure Require Import EPrimitive.
From MetaRocq.Erasure Require EProgram EEtaExpandedFix EReorderCstrs.
From MetaRocq.Common Require Import Primitive.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import ResultMonad.
From Equations Require Import Equations.
From Peregrine Require Import Utils.

Import ListNotations.
Import EnvMap.
Import MonadNotation.



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
        ; has_tCoFix      := false
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
        ; has_tCoFix      := false
        ; has_tPrim       := all_primitive_flags
        ; has_tLazy_Force := true
        |};
     has_cstr_params := false;  (* Agda already drops constructor params *)
     cstr_as_blocks  := false;
  |}.


Section Wf.

  Definition wf_fix_gen_ (wf : nat -> term -> result' unit) k mfix idx :=
    let k' := List.length mfix + k in
    assert' (idx <? #|mfix|) (fun _ => "Fixpoint index out of bounds") ;;
    result_forall (fun d => (wf k') d.(dbody)) mfix.

  Definition has_prim_ {epfl : EPrimitiveFlags} (p : prim_val term) : result' unit :=
    match prim_val_tag p with
    | primInt => assert' has_primint (fun _ => "Program contains primitive integers")
    | primFloat => assert' has_primfloat (fun _ => "Program contains primitive floats")
    | primString => assert' has_primstring (fun _ => "Program contains primitive strings")
    | primArray => assert' has_primarray (fun _ => "Program contains primitive arrays")
    end.

  Fixpoint wellformed {efl  : EEnvFlags} Σ (k : nat) (t : term) {struct t} : result' unit :=
    match t with
    | tRel i => assert' has_tRel (fun _ => "Program contains tRel") ;; assert' (Nat.ltb i k) (fun _ => "Program not closed, invalid tRel " ^ (string_of_nat i))
    | tEvar ev args => assert' has_tEvar (fun _ => "Program contains tEvar") ;; result_forall (wellformed Σ k) args
    | tLambda _ M => assert' has_tLambda (fun _ => "Program contains tLambda") ;; wellformed Σ (S k) M
    | tApp u v =>
      assert' has_tApp (fun _ => "Program contains tApp") ;;
      wellformed Σ k u ;;
      wellformed Σ k v
    | tLetIn na b b' =>
      assert' has_tLetIn (fun _ => "Program contains tLetIn") ;;
      wellformed Σ k b ;;
      wellformed Σ (S k) b'
    | tCase ind c brs =>
      assert' has_tCase (fun _ => "Program contains tCase") ;;
      let brs' := result_forall (fun br => wellformed Σ (#|br.1| + k) br.2) brs in
      assert' (wf_brs Σ ind.1 #|brs|) (fun _ => "Case not exhaustive") ;;
      wellformed Σ k c ;;
      brs'
    | tProj p c =>
      assert' has_tProj (fun _ => "Program contains tProj") ;;
      assert_some (lookup_projection Σ p) (fun _ => "Projection " ^ (string_of_inductive p.(proj_ind))^":"^(string_of_nat p.(proj_npars))^","^(string_of_nat p.(proj_arg)) ^ " not found") ;;
      wellformed Σ k c
    | tFix mfix idx =>
      assert' has_tFix (fun _ => "Program contains tFix") ;;
      result_forall (fun t => assert' ((isLambda ∘ dbody) t) (fun _ => "Fixpoint body is not a lambda")) mfix ;;
      wf_fix_gen_ (wellformed Σ) k mfix idx
    | tCoFix mfix idx =>
      assert' has_tCoFix (fun _ => "Program contains tCoFix (peregrine does not support cofixpoints)") ;;
      wf_fix_gen_ (wellformed Σ) k mfix idx
    | tBox => assert' has_tBox (fun _ => "Program contains tBox")
    | tConst kn =>
      assert' has_tConst (fun _ => "Program contains tConst") ;;
      match lookup_constant Σ kn with
      | Some d => assert' (has_axioms || isSome d.(cst_body)) (fun _ => "Invalid axiom " ^ (string_of_kername kn))
      | _ => Err ("Constant not found in environment " ^ (string_of_kername kn))
      end
    | tConstruct ind c block_args =>
      assert' has_tConstruct (fun _ => "Program contains tConstruct") ;;
      assert_some (lookup_constructor Σ ind c) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not found") ;;
      if cstr_as_blocks then
        match lookup_constructor_pars_args Σ ind c with
        | Some (p, a) => assert' ((p + a) == #|block_args|) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not fully applied")
        | _ => Ok tt end
        ;; result_forall (wellformed Σ k) block_args
      else assert' (is_nil block_args) (fun _ => "Constructor args non-empty")
    | tVar _ => assert' has_tVar (fun _ => "Program contains tVar")
    | tPrim p => has_prim_ p ;; assert' (test_prim (fun t => bool_of_result (wellformed Σ k t)) p) (fun _ => "Invalid array primitive")
    | tLazy t => assert' has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed Σ k t
    | tForce t => assert' has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed Σ k t
    end.

  Definition wf_projections idecl : result' unit :=
    match idecl.(ind_projs) with
    | [] => Ok tt
    | _ =>
      match idecl.(ind_ctors) with
      | [cstr] => assert' (#|idecl.(ind_projs)| == cstr.(cstr_nargs)) (fun _ => "Number of primitive projections doesn't match constructor args")
      | _ => Err "Invalid projection"
      end
    end.

  Definition wf_inductive (idecl : one_inductive_body) : result' unit :=
    wf_projections idecl.

  Definition wf_minductive {efl  : EEnvFlags} (mdecl : mutual_inductive_body) : result' unit :=
    assert' (has_cstr_params || (mdecl.(ind_npars) == 0)) (fun _ => "Has constructor params") ;;
    result_forall wf_inductive mdecl.(ind_bodies).

  Definition wf_global_decl {efl  : EEnvFlags} Σ d : result' unit :=
    match d with
    | ConstantDecl cb =>
      match cb.(cst_body) with
      | None => assert' has_axioms (fun _ => "Program contains axioms")
      | Some cb => wellformed Σ 0 cb
      end
    | InductiveDecl idecl => wf_minductive idecl
    end.

  Fixpoint check_fresh_global (k : kername) (decls : global_declarations) : result' unit :=
    match decls with
    | []    => Ok tt
    | p::ds =>
      assert' (negb (eq_kername (fst p) k)) (fun _ => "Duplicate definition " ^ (string_of_kername (fst p))) ;;
      check_fresh_global k ds
    end.

  (** Reference checker: [check_fresh_global] and every [lookup_env] in
      [wellformed] scan the declaration list, so it is quadratic in the size
      of the environment.  The checker that runs is [check_wf_glob] below,
      which computes the same result (see [check_wf_glob_eq]). *)
  Fixpoint check_wf_glob_ref {efl : EEnvFlags} (decls : global_declarations) : result' unit :=
    match decls with
    | []    => Ok tt
    | p::ds =>
      check_wf_glob_ref ds ;;
      check_fresh_global (fst p) ds ;;
      map_error (fun e => "Error while checking " ^ (string_of_kername (fst p)) ^ ": " ^ e) (wf_global_decl ds (snd p))
    end.

  Definition check_wf_program_ref {efl : EEnvFlags} (p : program) : result' unit :=
    check_wf_glob_ref (fst p) ;; wellformed (fst p) 0 (snd p).

End Wf.

(** * The checker that runs: one pass with a kername-keyed map

  [check_wf_glob_map] walks the declarations oldest first and keeps an
  [EnvMap] of the declarations checked so far.  Freshness is map membership
  and the lookups of [wellformed] go to the map ([wellformed_with]), so the
  check takes O(n log n) kername comparisons instead of O(n^2).  It returns
  exactly what the reference checker returns, error messages included
  ([check_wf_glob_eq], [check_wf_program_eq]). *)

Section WfFast.

  Section LookupWith.
    Context (look : kername -> option global_decl).

    Definition lookup_constant_with kn : option constant_body :=
      match look kn with
      | Some (ConstantDecl cdecl) => Some cdecl
      | _ => None
      end.

    Definition lookup_minductive_with kn : option mutual_inductive_body :=
      match look kn with
      | Some (InductiveDecl mdecl) => Some mdecl
      | _ => None
      end.

    Definition lookup_inductive_with ind : option (mutual_inductive_body * one_inductive_body) :=
      match lookup_minductive_with (inductive_mind ind) with
      | Some mdecl =>
        match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
        | Some idecl => Some (mdecl, idecl)
        | None => None
        end
      | None => None
      end.

    Definition lookup_constructor_with ind c
      : option (mutual_inductive_body * one_inductive_body * constructor_body) :=
      match lookup_inductive_with ind with
      | Some (mdecl, idecl) =>
        match nth_error idecl.(ind_ctors) c with
        | Some cdecl => Some (mdecl, idecl, cdecl)
        | None => None
        end
      | None => None
      end.

    Definition lookup_constructor_pars_args_with ind c : option (nat * nat) :=
      match lookup_constructor_with ind c with
      | Some (mdecl, idecl, cdecl) => Some (mdecl.(ind_npars), cdecl.(cstr_nargs))
      | None => None
      end.

    Definition lookup_projection_with (p : projection)
      : option (mutual_inductive_body * one_inductive_body * constructor_body * projection_body) :=
      match lookup_constructor_with p.(proj_ind) 0 with
      | Some (mdecl, idecl, cdecl) =>
        match nth_error idecl.(ind_projs) p.(proj_arg) with
        | Some pdecl => Some (mdecl, idecl, cdecl, pdecl)
        | None => None
        end
      | None => None
      end.

    Definition wf_brs_with ind brsl : bool :=
      match lookup_inductive_with ind with
      | Some (mib, oib) => #|oib.(ind_ctors)| == brsl
      | None => false
      end.
  End LookupWith.

  (** [wellformed] with its lookups done by [look]. *)
  Fixpoint wellformed_with {efl : EEnvFlags} look (k : nat) (t : term) {struct t} : result' unit :=
    match t with
    | tRel i => assert' has_tRel (fun _ => "Program contains tRel") ;; assert' (Nat.ltb i k) (fun _ => "Program not closed, invalid tRel " ^ (string_of_nat i))
    | tEvar ev args => assert' has_tEvar (fun _ => "Program contains tEvar") ;; result_forall (wellformed_with look k) args
    | tLambda _ M => assert' has_tLambda (fun _ => "Program contains tLambda") ;; wellformed_with look (S k) M
    | tApp u v =>
      assert' has_tApp (fun _ => "Program contains tApp") ;;
      wellformed_with look k u ;;
      wellformed_with look k v
    | tLetIn na b b' =>
      assert' has_tLetIn (fun _ => "Program contains tLetIn") ;;
      wellformed_with look k b ;;
      wellformed_with look (S k) b'
    | tCase ind c brs =>
      assert' has_tCase (fun _ => "Program contains tCase") ;;
      let brs' := result_forall (fun br => wellformed_with look (#|br.1| + k) br.2) brs in
      assert' (wf_brs_with look ind.1 #|brs|) (fun _ => "Case not exhaustive") ;;
      wellformed_with look k c ;;
      brs'
    | tProj p c =>
      assert' has_tProj (fun _ => "Program contains tProj") ;;
      assert_some (lookup_projection_with look p) (fun _ => "Projection " ^ (string_of_inductive p.(proj_ind))^":"^(string_of_nat p.(proj_npars))^","^(string_of_nat p.(proj_arg)) ^ " not found") ;;
      wellformed_with look k c
    | tFix mfix idx =>
      assert' has_tFix (fun _ => "Program contains tFix") ;;
      result_forall (fun t => assert' ((isLambda ∘ dbody) t) (fun _ => "Fixpoint body is not a lambda")) mfix ;;
      wf_fix_gen_ (wellformed_with look) k mfix idx
    | tCoFix mfix idx =>
      assert' has_tCoFix (fun _ => "Program contains tCoFix (peregrine does not support cofixpoints)") ;;
      wf_fix_gen_ (wellformed_with look) k mfix idx
    | tBox => assert' has_tBox (fun _ => "Program contains tBox")
    | tConst kn =>
      assert' has_tConst (fun _ => "Program contains tConst") ;;
      match lookup_constant_with look kn with
      | Some d => assert' (has_axioms || isSome d.(cst_body)) (fun _ => "Invalid axiom " ^ (string_of_kername kn))
      | _ => Err ("Constant not found in environment " ^ (string_of_kername kn))
      end
    | tConstruct ind c block_args =>
      assert' has_tConstruct (fun _ => "Program contains tConstruct") ;;
      assert_some (lookup_constructor_with look ind c) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not found") ;;
      if cstr_as_blocks then
        match lookup_constructor_pars_args_with look ind c with
        | Some (p, a) => assert' ((p + a) == #|block_args|) (fun _ => "Constructor " ^ (string_of_inductive ind)^":"^(string_of_nat c) ^ " not fully applied")
        | _ => Ok tt end
        ;; result_forall (wellformed_with look k) block_args
      else assert' (is_nil block_args) (fun _ => "Constructor args non-empty")
    | tVar _ => assert' has_tVar (fun _ => "Program contains tVar")
    | tPrim p => has_prim_ p ;; assert' (test_prim (fun t => bool_of_result (wellformed_with look k t)) p) (fun _ => "Invalid array primitive")
    | tLazy t => assert' has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed_with look k t
    | tForce t => assert' has_tLazy_Force (fun _ => "Program contains lazy/force") ;; wellformed_with look k t
    end.

  Definition wf_global_decl_with {efl : EEnvFlags} look d : result' unit :=
    match d with
    | ConstantDecl cb =>
      match cb.(cst_body) with
      | None => assert' has_axioms (fun _ => "Program contains axioms")
      | Some cb => wellformed_with look 0 cb
      end
    | InductiveDecl idecl => wf_minductive idecl
    end.

  (** Checks [decls] and returns the map of its declarations. *)
  Fixpoint check_wf_glob_map {efl : EEnvFlags} (decls : global_declarations)
    : result' (EnvMap.t global_decl) :=
    match decls with
    | []    => Ok EnvMap.empty
    | p::ds =>
      m <- check_wf_glob_map ds ;;
      match EnvMap.lookup (fst p) m with
      | Some _ => Err ("Duplicate definition " ^ (string_of_kername (fst p)))
      | None => Ok tt
      end ;;
      map_error (fun e => "Error while checking " ^ (string_of_kername (fst p)) ^ ": " ^ e)
        (wf_global_decl_with (fun kn => EnvMap.lookup kn m) (snd p)) ;;
      Ok (EnvMap.add (fst p) (snd p) m)
    end.

  Definition check_wf_glob {efl : EEnvFlags} (decls : global_declarations) : result' unit :=
    _ <- check_wf_glob_map decls ;; Ok tt.

  Definition check_wf_program {efl : EEnvFlags} (p : program) : result' unit :=
    m <- check_wf_glob_map (fst p) ;;
    wellformed_with (fun kn => EnvMap.lookup kn m) 0 (snd p).

  (** ** The fast checker computes what the reference checker computes *)

  Section LookupWithEq.
    Context (Σ : global_declarations) (look : kername -> option global_decl).
    Context (hlook : forall kn, look kn = lookup_env Σ kn).

    Lemma lookup_constant_with_eq kn : lookup_constant_with look kn = lookup_constant Σ kn.
    Proof. unfold lookup_constant_with, lookup_constant. rewrite hlook. now destruct lookup_env as [[]|]. Qed.

    Lemma lookup_minductive_with_eq kn : lookup_minductive_with look kn = lookup_minductive Σ kn.
    Proof. unfold lookup_minductive_with, lookup_minductive. rewrite hlook. now destruct lookup_env as [[]|]. Qed.

    Lemma lookup_inductive_with_eq ind : lookup_inductive_with look ind = lookup_inductive Σ ind.
    Proof.
      unfold lookup_inductive_with, lookup_inductive. rewrite lookup_minductive_with_eq.
      destruct lookup_minductive => //=; destruct nth_error => //.
    Qed.

    Lemma lookup_constructor_with_eq ind c : lookup_constructor_with look ind c = lookup_constructor Σ ind c.
    Proof.
      unfold lookup_constructor_with, lookup_constructor. rewrite lookup_inductive_with_eq.
      destruct lookup_inductive as [[]|] => //=; destruct nth_error => //.
    Qed.

    Lemma lookup_constructor_pars_args_with_eq ind c :
      lookup_constructor_pars_args_with look ind c = lookup_constructor_pars_args Σ ind c.
    Proof.
      unfold lookup_constructor_pars_args_with, lookup_constructor_pars_args.
      rewrite lookup_constructor_with_eq. now destruct lookup_constructor as [[[]]|].
    Qed.

    Lemma lookup_projection_with_eq p : lookup_projection_with look p = lookup_projection Σ p.
    Proof.
      unfold lookup_projection_with, lookup_projection. rewrite lookup_constructor_with_eq.
      destruct lookup_constructor as [[[]]|] => //=; destruct nth_error => //.
    Qed.

    Lemma wf_brs_with_eq {efl : EEnvFlags} ind n : wf_brs_with look ind n = wf_brs Σ ind n.
    Proof. unfold wf_brs_with, wf_brs. now rewrite lookup_inductive_with_eq. Qed.

    Lemma result_forall_ext_All {A} (f g : A -> result' unit) l :
      All (fun x => f x = g x) l -> result_forall f l = result_forall g l.
    Proof.
      unfold result_forall. generalize (@Ok unit string tt).
      intros r hl; induction hl in r |- *; cbn; auto. now rewrite p.
    Qed.

    Lemma wellformed_with_eq {efl : EEnvFlags} t k : wellformed_with look k t = wellformed Σ k t.
    Proof.
      induction t using EInduction.term_forall_list_ind in k |- *; cbn;
        rewrite ?lookup_constant_with_eq ?lookup_constructor_with_eq
          ?lookup_constructor_pars_args_with_eq ?lookup_projection_with_eq ?wf_brs_with_eq;
        rewrite ?IHt ?IHt1 ?IHt2; auto.
      - (* tEvar *)
        rewrite (result_forall_ext_All (wellformed_with look k) (wellformed Σ k) l) //.
        eapply All_impl; [exact X|]. intros x h; apply h.
      - (* tConstruct *)
        destruct cstr_as_blocks => //.
        rewrite (result_forall_ext_All (wellformed_with look k) (wellformed Σ k) args) //.
        eapply All_impl; [exact X|]. intros x h; apply h.
      - (* tCase *)
        rewrite (result_forall_ext_All (fun br => wellformed_with look (#|br.1| + k) br.2)
          (fun br => wellformed Σ (#|br.1| + k) br.2) l) //.
        eapply All_impl; [exact X|]. intros x h; apply h.
      - (* tFix *)
        rewrite (result_forall_ext_All (fun d => wellformed_with look (#|m| + k) (dbody d))
          (fun d => wellformed Σ (#|m| + k) (dbody d)) m) //.
        eapply All_impl; [exact X|]. intros x h; apply h.
      - (* tCoFix *)
        rewrite (result_forall_ext_All (fun d => wellformed_with look (#|m| + k) (dbody d))
          (fun d => wellformed Σ (#|m| + k) (dbody d)) m) //.
        eapply All_impl; [exact X|]. intros x h; apply h.
      - (* tPrim *)
        enough (e : test_prim (fun t => bool_of_result (wellformed_with look k t)) p =
                    test_prim (fun t => bool_of_result (wellformed Σ k t)) p) by now rewrite e.
        inversion X; subst; cbn; auto.
        destruct X0 as [hd hv]. unfold test_array_model. rewrite hd. f_equal.
        eapply All_forallb_eq_forallb; [exact hv|]. intros x h. now rewrite h.
    Qed.

    Lemma wf_global_decl_with_eq {efl : EEnvFlags} d : wf_global_decl_with look d = wf_global_decl Σ d.
    Proof.
      destruct d as [[[b|]]|] => //=. apply wellformed_with_eq.
    Qed.
  End LookupWithEq.

  Lemma check_fresh_global_lookup k ds :
    check_fresh_global k ds =
    match lookup_env ds k with
    | Some _ => Err ("Duplicate definition " ^ (string_of_kername k))
    | None => Ok tt
    end.
  Proof.
    induction ds as [|[kn d] ds IH]; cbn => //.
    change (eq_kername k kn) with (eqb k kn). change (eq_kername kn k) with (eqb kn k).
    destruct (eqb_spec k kn).
    - subst. now rewrite eqb_refl.
    - destruct (eqb_spec kn k); [congruence|]. exact IH.
  Qed.

  Lemma check_wf_glob_map_spec {efl : EEnvFlags} decls :
    match check_wf_glob_map decls with
    | Ok m => check_wf_glob_ref decls = Ok tt /\ forall kn, EnvMap.lookup kn m = lookup_env decls kn
    | Err e => check_wf_glob_ref decls = Err e
    end.
  Proof.
    induction decls as [|[kn d] ds IH]; cbn.
    - split => //; intros; reflexivity.
    - destruct (check_wf_glob_map ds) as [m|e]; cbn; [|now rewrite IH].
      destruct IH as [-> hm]. cbn.
      rewrite check_fresh_global_lookup -hm.
      destruct EnvMap.lookup => //=.
      rewrite (wf_global_decl_with_eq ds _ hm).
      destruct wf_global_decl as [[]|] => //=.
      split => // kn'.
      change (eq_kername kn' kn) with (eqb kn' kn).
      destruct (eqb_spec kn' kn).
      + now apply EnvMap.gss.
      + rewrite EnvMap.gso //.
  Qed.

  Lemma check_wf_glob_eq {efl : EEnvFlags} decls : check_wf_glob decls = check_wf_glob_ref decls.
  Proof.
    unfold check_wf_glob. have := @check_wf_glob_map_spec efl decls.
    destruct check_wf_glob_map => //=. now intros [-> _].
  Qed.

  Lemma check_wf_program_eq {efl : EEnvFlags} p : check_wf_program p = check_wf_program_ref p.
  Proof.
    unfold check_wf_program, check_wf_program_ref. have := @check_wf_glob_map_spec efl p.1.
    destruct check_wf_glob_map => //=; [|now intros ->].
    intros [-> hm]. cbn. now apply wellformed_with_eq.
  Qed.

End WfFast.

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

  Definition inspect {A} (a : A) : {b | a = b} := @exist _ _ a eq_refl.

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

  Theorem check_wf_glob_ref_equiv {efl : EEnvFlags} : forall d,
    bool_of_result (check_wf_glob_ref d) = check_wf_glob_b d.
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

  Theorem check_wf_glob_equiv {efl : EEnvFlags} : forall d,
    bool_of_result (check_wf_glob d) = check_wf_glob_b d.
  Proof.
    intros d. rewrite check_wf_glob_eq. apply check_wf_glob_ref_equiv.
  Qed.

  Theorem check_wf_program_equiv {efl : EEnvFlags} : forall p,
    bool_of_result (check_wf_program p) = check_wf_program_b p.
  Proof.
    intros.
    rewrite check_wf_program_eq.
    unfold check_wf_program_ref, check_wf_program_b; cbn.
    rewrite <- check_wf_glob_ref_equiv.
    destruct check_wf_glob_ref; auto.
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

  Lemma check_wf_program_sound {efl : EEnvFlags} (p : program) :
    bool_of_result (check_wf_program p) = true -> EProgram.wf_eprogram efl p.
  Proof.
    rewrite check_wf_program_equiv. unfold check_wf_program_b, EProgram.wf_eprogram.
    intros h. apply andb_prop in h as [hg ht]. split; [|exact ht].
    now destruct (check_wf_globbP (fst p)).
  Qed.

End WfCorrect.

(** * Checking the precondition of the transformation pipelines

  The verified middle-end pipelines (see [Transforms.v]) require their input
  to be well formed, eta-expanded (in the sense of [EEtaExpandedFix], i.e. with
  fully applied constructors and fixpoints) and the constructor reordering
  mapping to be compatible with the environment.  [check_pipeline_pre] decides
  all of this; [check_pipeline_pre_sound] shows that it is sound.

  [check_pipeline_pre] and [check_eta_env] are kept only as a diagnostic: the
  pipeline no longer uses them.  Eta-expandedness is now established by the
  verified eta-expansion pass in front of the pipelines (EEtaExpand.v,
  [eta_expand_program_expanded]) instead of being checked, so the run
  functions of Transforms.v check [check_pipeline_wf] instead. *)

Section PipelinePre.
  Context {efl : EEnvFlags}.

  Fixpoint check_eta_env (Σ : global_declarations) : result' unit :=
    match Σ with
    | [] => Ok tt
    | (kn, d) :: Σ' =>
      assert' (EEtaExpandedFix.isEtaExp_decl Σ' d)
        (fun _ => ("Declaration " ++ string_of_kername kn ++
                  " is not eta-expanded (constructor or fixpoint not fully applied)")%bs) ;;
      check_eta_env Σ'
    end.

  Lemma check_eta_env_sound Σ :
    bool_of_result (check_eta_env Σ) = true -> EEtaExpandedFix.isEtaExp_env Σ.
  Proof.
    induction Σ as [|[kn d] Σ IH]; cbn => // h.
    rewrite result_bindb result_assertb' in h.
    apply andb_prop in h as [hd hΣ]. now rewrite hd (IH hΣ).
  Qed.

  Definition check_pipeline_pre (m : EProgram.inductives_mapping) (p : program) : result' unit :=
    assert' (EReorderCstrs.wf_inductives_mapping (fst p) m)
      (fun _ => "Constructor reordering mapping does not match the inductive declarations"%bs) ;;
    check_wf_program p ;;
    check_eta_env (fst p) ;;
    assert' (EEtaExpandedFix.isEtaExp (fst p) [] (snd p))
      (fun _ => "Program term is not eta-expanded (constructor or fixpoint not fully applied)").

  Lemma isEtaExp_env_expanded_global_env (Σ : global_declarations) :
    EEtaExpandedFix.isEtaExp_env Σ -> EEtaExpandedFix.expanded_global_env Σ.
  Proof.
    induction Σ as [|[kn d] Σ IH]; cbn.
    - intros _. constructor.
    - intros h. apply andb_prop in h as [hd hΣ]. constructor; [now apply IH|].
      destruct d as [cb|]; cbn in * => //.
      unfold EEtaExpandedFix.isEtaExp_constant_decl, EEtaExpandedFix.expanded_constant_decl in *.
      destruct (cst_body cb); cbn in * => //.
      now apply EEtaExpandedFix.isEtaExp_expanded.
  Qed.

  Lemma check_pipeline_pre_sound m p :
    bool_of_result (check_pipeline_pre m p) = true ->
    EReorderCstrs.wf_inductives_mapping (fst p) m /\
    EProgram.wf_eprogram efl p /\
    EEtaExpandedFix.expanded_eprogram p.
  Proof.
    unfold check_pipeline_pre.
    rewrite !result_bindb !result_assertb'.
    intros h. apply andb_prop in h as [hm h]. apply andb_prop in h as [hwf h].
    apply andb_prop in h as [he ht].
    split; [exact hm|]. split.
    { now apply check_wf_program_sound. }
    split; [now apply isEtaExp_env_expanded_global_env, check_eta_env_sound|].
    now apply EEtaExpandedFix.isEtaExp_expanded.
  Qed.

  (** The well-formedness part of the precondition alone: eta-expandedness
      is established by the verified eta-expansion pass that runs first
      ([EEtaExpand]), so it needs no check. *)
  Definition check_pipeline_wf (m : EProgram.inductives_mapping) (p : program) : result' unit :=
    assert' (EReorderCstrs.wf_inductives_mapping (fst p) m)
      (fun _ => "Constructor reordering mapping does not match the inductive declarations"%bs) ;;
    check_wf_program p.

  Lemma check_pipeline_wf_sound m p :
    bool_of_result (check_pipeline_wf m p) = true ->
    EReorderCstrs.wf_inductives_mapping (fst p) m /\ EProgram.wf_eprogram efl p.
  Proof.
    unfold check_pipeline_wf.
    rewrite result_bindb. rewrite (result_assertb' (E := string)).
    intros h. apply andb_prop in h as [hm hwf].
    split; [exact hm|]. now apply check_wf_program_sound.
  Qed.
End PipelinePre.

(** Run [k] on a proof of [P] if the check [r] succeeds, and propagate its
    error otherwise. *)
Definition with_check {A P : Type} (r : result' unit)
  (sound : bool_of_result r = true -> P) (k : P -> A) : result' A :=
  match r as r' return r = r' -> result' A with
  | Ok _ => fun e => Ok (k (sound (f_equal bool_of_result e)))
  | Err msg => fun _ => Err msg
  end eq_refl.



Module CheckWfExAst.
  Import ExAst.

  Definition check_wf_typed_program {efl : EEnvFlags} (p : global_env) : result' unit  :=
    check_wf_glob (trans_env p).

End CheckWfExAst.
