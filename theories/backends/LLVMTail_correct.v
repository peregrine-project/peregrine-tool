(* Correctness of [LLVMTail]: Vellvm's denotation of a call ignores its
   annotations, so marking calls [tail] leaves the behaviour of the program in
   Vellvm unchanged, and the correctness theorem of the LLVM backend extends to
   the marked module.  What the marker promises to LLVM stays outside the theorem,
   since Vellvm gives [tail] no semantics. *)
From Stdlib Require Import List String ZArith FunctionalExtensionality.
From ITree Require Import ITree Eq.Eqit.
From ExtLib Require Import Structures.Monads.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.
From CertiRocq.LambdaANF Require Import term eval.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_sim_exp.
From Peregrine Require LLVMTail.
Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

(* Two instructions are related when they are equal up to the annotations of a call. *)
Definition same_instr {T : Set} (a b : instr_id * instr T * list (metadata T)) : Prop :=
  a = b \/
  exists id f args an an' obs md,
    a = (id, INSTR_Call f args an obs, md) /\ b = (id, INSTR_Call f args an' obs, md).

Definition same_block {T : Set} (a b : LLVMAst.block T) : Prop :=
  blk_id a = blk_id b /\ blk_phis a = blk_phis b /\ blk_term a = blk_term b /\
  blk_comments a = blk_comments b /\ Forall2 same_instr (blk_code a) (blk_code b).

Lemma same_code_refl {T : Set} (c : LLVMAst.code T) : Forall2 same_instr c c.
Proof. induction c; constructor; [left; reflexivity | assumption]. Qed.

Lemma same_block_refl {T : Set} (b : LLVMAst.block T) : same_block b b.
Proof. repeat split; apply same_code_refl. Qed.

Lemma tail_code_same t (c : LLVMAst.code typ) r : Forall2 same_instr c (LLVMTail.tail_code t c r).
Proof.
  unfold LLVMTail.tail_code.
  destruct (rev c) as [|[[id ins] md] rest] eqn:E; try apply same_code_refl.
  assert (Ec : c = rev ((id, ins, md) :: rest))
    by (rewrite <- E, rev_involutive; reflexivity).
  destruct id as [x|]; try apply same_code_refl.
  destruct ins; try apply same_code_refl.
  destruct anns; try apply same_code_refl.
  destruct (LLVMTail.raw_id_eqb x r); try apply same_code_refl.
  destruct (forallb (LLVMTail.tail_arg t) args); try apply same_code_refl.
  rewrite Ec at 1. simpl rev. apply Forall2_app; [apply same_code_refl|].
  constructor; [|constructor]. right. do 7 eexists. split; reflexivity.
Qed.

Lemma tail_block_same t (b : LLVMAst.block typ) : same_block b (LLVMTail.tail_block t b).
Proof.
  unfold LLVMTail.tail_block.
  destruct (blk_term b) as [[x0 tm] md0] eqn:E.
  destruct tm; try apply same_block_refl.
  destruct v as [ty ex]; destruct ex; try apply same_block_refl.
  destruct id; try apply same_block_refl.
  repeat split; cbn; auto using tail_code_same.
Qed.

Lemma Forall2_map2 {A B C D : Type} (P : A -> B -> Prop) (Q : C -> D -> Prop) g h l l' :
  (forall a b, P a b -> Q (g a) (h b)) -> Forall2 P l l' -> Forall2 Q (map g l) (map h l').
Proof. induction 2; constructor; auto. Qed.

Lemma Forall2_tail_blocks t (bs : list (LLVMAst.block typ)) :
  Forall2 same_block bs (map (LLVMTail.tail_block t) bs).
Proof. induction bs; constructor; auto using tail_block_same. Qed.

(* The conversion to dynamic types preserves the relation. *)
Lemma same_code_tfmap (f : typ -> dtyp) (c c' : LLVMAst.code typ) :
  Forall2 same_instr c c' -> Forall2 same_instr (tfmap f c) (tfmap f c').
Proof.
  induction 1 as [|a b c c' H _ IH]; [constructor|].
  cbn. constructor; [|exact IH].
  destruct H as [<-|(id & f0 & args & an & an' & obs & md & -> & ->)]; [left; reflexivity|right].
  cbn. do 7 eexists. split; reflexivity.
Qed.

Lemma same_block_tfmap (f : typ -> dtyp) (b b' : LLVMAst.block typ) :
  same_block b b' -> same_block (tfmap f b) (tfmap f b').
Proof.
  intros (A & B & C & D & E). unfold same_block. cbn.
  rewrite A, B, C, D. repeat split. apply same_code_tfmap. exact E.
Qed.

(* Definitions before and after the construction of the control-flow graph. *)
Definition same_src_def {T : Set}
    (d d' : definition T (LLVMAst.block T * list (LLVMAst.block T))) : Prop :=
  df_prototype d = df_prototype d' /\ df_args d = df_args d' /\
  same_block (fst (df_instrs d)) (fst (df_instrs d')) /\
  Forall2 same_block (snd (df_instrs d)) (snd (df_instrs d')).

Definition same_def {T : Set} (d d' : definition T (CFG.cfg T)) : Prop :=
  df_prototype d = df_prototype d' /\ df_args d = df_args d' /\
  CFG.init (df_instrs d) = CFG.init (df_instrs d') /\
  CFG.args (df_instrs d) = CFG.args (df_instrs d') /\
  Forall2 same_block (CFG.blks (df_instrs d)) (CFG.blks (df_instrs d')).

Lemma definitions_tail (L : LLprog) :
  Forall2 same_src_def (flat_map (@definitions_of typ _) L)
                       (flat_map (@definitions_of typ _) (map LLVMTail.tail_tle L)).
Proof.
  induction L as [|e L IH]; [constructor|].
  destruct e; cbn; auto.
  destruct (df_instrs defn) as [b bs] eqn:E. cbn. constructor; [|exact IH].
  unfold same_src_def. cbn. rewrite E. cbn.
  exact (conj eq_refl (conj eq_refl (conj (tail_block_same _ _) (Forall2_tail_blocks _ _)))).
Qed.

Lemma flat_map_tail {A : Type} (sel : toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)) -> list A) (L : LLprog) :
  (forall e, sel (LLVMTail.tail_tle e) = sel e) ->
  flat_map sel (map LLVMTail.tail_tle L) = flat_map sel L.
Proof. intros H. induction L; cbn; [reflexivity|]. rewrite H, IHL. reflexivity. Qed.

Lemma tail_tle_definition_cases (e : toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))) :
  (forall d, e <> TLE_Definition d) -> LLVMTail.tail_tle e = e.
Proof.
  destruct e; try reflexivity. intros H. exfalso. exact (H _ eq_refl).
Qed.

Definition same_mcfg (a b : CFG.mcfg dtyp) : Prop :=
  m_globals a = m_globals b /\ m_declarations a = m_declarations b /\
  Forall2 same_def (m_definitions a) (m_definitions b).

Lemma same_convert (L : LLprog) :
  same_mcfg (convert_types (CFG.mcfg_of_tle L))
            (convert_types (CFG.mcfg_of_tle (map LLVMTail.tail_tle L))).
Proof.
  unfold convert_types, CFG.mcfg_of_tle, CFG.mcfg_of_modul, CFG.modul_of_toplevel_entities.
  cbn [m_type_defs m_globals m_declarations m_definitions].
  rewrite (flat_map_tail (@type_defs_of typ _)) by (destruct e; cbn; try reflexivity; destruct (df_instrs defn); reflexivity).
  rewrite (flat_map_tail (@globals_of typ _)) by (destruct e; cbn; try reflexivity; destruct (df_instrs defn); reflexivity).
  rewrite (flat_map_tail (@declarations_of typ _)) by (destruct e; cbn; try reflexivity; destruct (df_instrs defn); reflexivity).
  unfold same_mcfg. repeat split.
  simpl convert_typ. cbn.
  refine (@Forall2_map2 _ _ _ _ (@same_def typ) (@same_def dtyp) _ _ _ _ _ _).
  { intros d d' (P & A & I & Ar & B). unfold same_def. cbn.
    rewrite P, A, I, Ar. repeat split.
    refine (@Forall2_map2 _ _ _ _ (@same_block typ) (@same_block dtyp) _ _ _ _ (same_block_tfmap _) B). }
  refine (@Forall2_map2 _ _ _ _ (@same_src_def typ) (@same_def typ) _ _ _ _ _ (definitions_tail L)).
  intros d d' (P & A & H & B). unfold same_def. cbn.
  unfold CFG.init_of_definition. rewrite P, A, (proj1 H). repeat split.
  constructor; assumption.
Qed.

(* The denotation ignores the annotations of a call. *)
Lemma denote_instr_same (a b : instr_id * instr dtyp * list (metadata dtyp)) v :
  same_instr a b -> denote_instr a v = denote_instr b v.
Proof.
  intros [<-|(id & f & args & an & an' & obs & md & -> & ->)]; [reflexivity|].
  destruct f as [dt f]. destruct id; reflexivity.
Qed.

Lemma denote_code_same (c c' : LLVMAst.code dtyp) v :
  Forall2 same_instr c c' -> denote_code c v = denote_code c' v.
Proof.
  unfold denote_code. induction 1; cbn [loop_monad]; [reflexivity|].
  rewrite (@denote_instr_same _ _ v H), IHForall2. reflexivity.
Qed.

Lemma denote_block_same (b b' : LLVMAst.block dtyp) f v :
  same_block b b' -> denote_block b f v = denote_block b' f v.
Proof.
  intros (A & B & C & D & E). unfold denote_block.
  rewrite (@denote_code_same _ _ v E), B, C. reflexivity.
Qed.

Definition find_rel (x y : option (LLVMAst.block dtyp)) : Prop :=
  match x, y with
  | Some b, Some b' => same_block b b'
  | None, None => True
  | _, _ => False
  end.

Lemma ocfg_map_same (bs bs' : list (LLVMAst.block dtyp)) :
  Forall2 same_block bs bs' ->
  forall k, find_rel (RM.find k (CFG.ocfg_map bs)) (RM.find k (CFG.ocfg_map bs')).
Proof.
  unfold CFG.ocfg_map. induction 1 as [|x y l l' H _ IH]; intros k; cbn [fold_right].
  - rewrite !RMF.F.empty_o. exact I.
  - rewrite !RMF.F.add_o. rewrite (proj1 H).
    match goal with |- context [if ?c then _ else _] => destruct c end.
    + exact H.
    + apply IH.
Qed.

Lemma denote_ocfg_map_same m m' v :
  (forall k, find_rel (RM.find k m) (RM.find k m')) ->
  denote_ocfg_map m v = denote_ocfg_map m' v.
Proof.
  intros H. unfold denote_ocfg_map. f_equal. apply functional_extensionality.
  intros [f s]. specialize (H s).
  destruct (RM.find s m), (RM.find s m'); cbn in H; try contradiction; [|reflexivity].
  rewrite (@denote_block_same _ _ f v H). reflexivity.
Qed.

Lemma denote_function_same (d d' : definition dtyp (CFG.cfg dtyp)) :
  same_def d d' -> denote_function d = denote_function d'.
Proof.
  intros (P & A & I & Ar & B). unfold denote_function. cbv zeta.
  apply functional_extensionality; intros params.
  assert (Hp : push_call_frame d params = push_call_frame d' params)
    by (unfold push_call_frame; rewrite A, ?P; reflexivity).
  assert (Hm : denote_ocfg_map (CFG.ocfg_map (CFG.blks (df_instrs d)))
             = denote_ocfg_map (CFG.ocfg_map (CFG.blks (df_instrs d'))))
    by (apply functional_extensionality; intros v;
        apply denote_ocfg_map_same, ocfg_map_same, B).
  rewrite Hp. unfold denote_cfg_map. rewrite Hm, I. reflexivity.
Qed.

Lemma address_same (d d' : definition dtyp (CFG.cfg dtyp)) :
  same_def d d' -> address_one_function d = address_one_function d'.
Proof.
  intros H. pose proof (@denote_function_same _ _ H) as F. destruct H as (P & _).
  unfold address_one_function. rewrite P, F. reflexivity.
Qed.

Lemma map_monad_address (l l' : list (definition dtyp (CFG.cfg dtyp))) :
  Forall2 same_def l l' ->
  map_monad address_one_function l = map_monad address_one_function l'.
Proof.
  induction 1; cbn [map_monad]; [reflexivity|].
  rewrite (@address_same _ _ H), IHForall2. reflexivity.
Qed.

Lemma prototypes_same (l l' : list (definition dtyp (CFG.cfg dtyp))) :
  Forall2 same_def l l' -> map df_prototype l = map df_prototype l'.
Proof. induction 1; cbn; [reflexivity|]. rewrite (proj1 H), IHForall2. reflexivity. Qed.

Lemma denote_with_runtime_same rt dt entry params (a b : CFG.mcfg dtyp) :
  same_mcfg a b ->
  denote_with_runtime rt dt entry params a = denote_with_runtime rt dt entry params b.
Proof.
  intros (G & D & F). unfold denote_with_runtime, build_global_environment.
  rewrite G, D, (@prototypes_same _ _ F), (@map_monad_address _ _ F). reflexivity.
Qed.

Lemma filter_tail (P : toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)) -> bool)
    (L : LLprog) :
  (forall e, P (LLVMTail.tail_tle e) = P e) ->
  List.filter P (map LLVMTail.tail_tle L) = map LLVMTail.tail_tle (List.filter P L).
Proof.
  intros H. induction L as [|e L IH]; [reflexivity|]. cbn [List.map List.filter].
  rewrite H. destruct (P e); cbn [List.map]; rewrite IH; reflexivity.
Qed.

Lemma link_tail p :
  link runtime_prelude (map LLVMTail.tail_tle p)
  = map LLVMTail.tail_tle (link runtime_prelude p).
Proof.
  unfold link. cbv zeta. rewrite map_app.
  replace (map LLVMTail.tail_tle runtime_prelude) with runtime_prelude by reflexivity.
  f_equal.
  apply filter_tail. intros e.
  destruct e; try reflexivity. cbn. destruct (df_instrs defn); reflexivity.
Qed.

Theorem tail_run_program gc make_tinfo (p : LLprog) :
  run_program gc make_tinfo (map LLVMTail.tail_tle p) = run_program gc make_tinfo p.
Proof.
  unfold run_program. rewrite link_tail. f_equal. f_equal.
  apply functional_extensionality; intros tinfo. symmetry.
  apply denote_with_runtime_same, same_convert.
Qed.

(* The correctness theorem of the LLVM backend holds of the marked module. *)
Theorem LambdaANF_to_LLVM_tail_correct :
  forall (cenv : ctor_env) (pfs : prims) prim_of
         (heap_inv : Memory.state -> ptr -> Prop)
         (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
         (fds : fundefs) (main : term.exp) (v : term.val) (n : nat),
    runtime_correct cenv fds heap_inv gc make_tinfo ->
    llvm_restricted cenv fds main ->
    bstep_e pfs cenv (M.empty _) (Efun fds main) v n ->
    let marked := map LLVMTail.tail_tle (emitted cenv prim_of (Efun fds main)) in
    ends_in_oom (run_program gc make_tinfo marked)
    \/ exists st ls genv z,
        returns (run_program gc make_tinfo marked) ((st, (ls, genv)), I64 z) /\
        repr_val cenv fds genv st v z.
Proof.
  intros. subst marked. rewrite tail_run_program.
  eapply LambdaANF_to_LLVM_correct; eauto.
Qed.
