From Stdlib Require Import List String Arith Lia Cyclic.Int63.Uint63.
Import ListNotations.
From Equations Require Import Equations.
Import Logic.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring.
From MetaRocq.Erasure Require Import EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.

From Malfunction Require Import utils_array Malfunction.
Open Scope bs.

Section MapiInP.
  Context {A B : Type}.

  Equations mapi_InP (l : list A) (n : nat) (f : nat -> forall x : A, In x l -> B) : list B :=
  mapi_InP nil n _ := nil;
  mapi_InP (cons x xs) n f := cons (f n x _) (mapi_InP xs (S n) (fun n x inx => f n x _)).
End MapiInP.

Lemma mapi_InP_spec' {A B : Type} (f : nat -> A -> B) (l : list A) n :
  mapi_InP l n (fun n (x : A) _ => f n x) = mapi_rec f l n.
Proof.
  remember (fun n (x : A) _ => f n x) as g.
  funelim (mapi_InP l n g); simpl. reflexivity.
  simp mapi_InP.
  f_equal. 
  now rewrite (H f0).
Qed.

Lemma mapi_InP_spec {A B : Type} (f : nat -> A -> B) (l : list A) :
  mapi_InP l 0 (fun n (x : A) _ => f n x) = mapi f l.
Proof.
  eapply mapi_InP_spec'.
Qed.

Definition Mapply_ '(e, l) :=
    match l with [] => e | _ => Mapply (e, l) end.

Definition Mlambda_ '(e, l) :=
    match e with [] => l | _ => Mlambda (e, l) end.

Definition blocks_until i (num_args : list nat) :=
  #| filter (fun x => match x with 0 => false | _ => true end) (firstn i num_args)|.

Definition nonblocks_until i num_args :=
    #| filter (fun x => match x with 0 => true | _ => false end) (firstn i num_args)|.

Definition Mcase : list nat * t * list (list Ident.t * t) -> t :=
 fun '(num_args, discr, brs) =>
   Mswitch (discr, mapi (fun i '(nms, b) => 
      (match nth_error num_args i with
      | Some 0 =>  [Malfunction.Intrange (int_of_nat (nonblocks_until i num_args), int_of_nat (nonblocks_until i num_args))]
      | _hasargs => [Malfunction.Tag (int_of_nat (blocks_until i num_args))]
      end,
      Mapply_ (Mlambda_ (nms, b), mapi (fun i _ => Mfield (int_of_nat i, discr)) (nms)))) brs).

From MetaRocq Require Import EAst.

Section Compile.
  Context (Σ : global_declarations).

  Definition lookup_record_projs (e : global_declarations) (ind : Kernames.inductive) : option (list Kernames.ident) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map proj_name idecl.(ind_projs))
    | None => None
    end.

  Definition lookup_constructor_args (e : global_declarations) (ind : Kernames.inductive) : option (list nat) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map cstr_nargs idecl.(ind_ctors))
    | None => None
    end.

  Definition Mapply_u t a :=
    match t with Mapply (fn, args) => Mapply (fn, List.app args [a]) | _ => Mapply (t, [a]) end.

  Obligation Tactic := idtac.

  Definition num_of_nat n := Mnum (numconst_Int (int_of_nat n)).

  Definition compile_array (values : list Malfunction.t) (default : Malfunction.t) : Malfunction.t :=
    let init := Mvecnew (Array, num_of_nat (List.length values), default) in
    fold_left_i (fun v idx arr => Mvecset (Array, arr, num_of_nat idx, v)) values init.

  (* Definition to_primitive (compile : term -> Malfunction.t) 
    (v : EPrimitive.prim_val EAst.term) : Malfunction.t := *)

  Fixpoint is_wf_rec_body (t : Malfunction.t) : bool :=
    match t with
    | Mlambda _ => true
    | Mlazy _ => true
    | Mlet (_bindings, t) => is_wf_rec_body t
    | _ => false
    end.

  Definition force_lambda (t : Malfunction.t) :=
    if is_wf_rec_body t then t
    else Mlambda (["__expanded"], Mapply_u t (Mvar "__expanded")).
  
  (* Import Sigma_Notations.
  Import ZArith.
  Equations? char63_valid_to_byte (s : PrimString.char63) (v : PrimStringAxioms.char63_valid s): Byte.byte :=
    | s | v with inspect (Byte.of_nat (Uint63.to_nat s)) :=
      { | exist (Some x) _ => x
        | exist None hnone => False_rect _ _ }.
  Proof.
    red in v. 
    apply Byte.of_nat_None_iff in hnone.
    rewrite <- v in hnone; clear v.
    rewrite <- (Nat2Z.id 255) in hnone.
    eapply Z2Nat.inj_lt in hnone; auto with zarith.
    rewrite Int63.land_spec' in hnone.
    rewrite (Z.land_ones _ 8) in hnone; lia.
  Qed. *)

  Definition char63_to_byte (s : PrimString.char63) : Byte.byte :=
    match Byte.of_nat (Uint63.to_nat s) with
    | None => Byte.x00
    | Some x => x
    end.

  Definition string_of_primstring (s : PrimString.string) : string :=
    String.parse (List.map char63_to_byte (PrimStringAxioms.to_list s)).

  Equations? compile (t: term) : Malfunction.t
    by wf t (fun x y : EAst.term => size x < size y) :=
      | tVar na => Mvar na
      | tLambda nm bod => Mlambda ([(BasicAst.string_of_name nm)], compile bod)
      | tLetIn nm dfn bod => Mlet ([Named ((BasicAst.string_of_name nm), compile dfn)], compile bod)
      | tApp fn arg =>
          Mapply_u (compile fn) (compile arg)
      | tConst nm => Mglobal (Kernames.string_of_kername nm)
      | tConstruct i m [] =>
        match lookup_constructor_args Σ i with
        | Some num_args => Mnum (numconst_Int (int_of_nat (nonblocks_until m num_args)))
        | None => Mstring "error: inductive not found"
        end
      | tConstruct i m args =>
        match lookup_constructor_args Σ i with
        | Some num_args => Mblock (int_of_nat (blocks_until m num_args), map_InP args (fun x H => compile x))
        | None => Mstring "error: inductive not found"
        end
      | tCase i mch [] => Mlambda (["empty_match"], Mvar "empty_match")
      | tCase i mch brs =>
        match lookup_constructor_args Σ (fst i) with
        | Some num_args =>
            Mcase (num_args, compile mch, map_InP brs (fun br H => (rev_map (fun nm => (BasicAst.string_of_name nm)) (fst br), compile (snd br))))     
       | None => Mstring "error: inductive not found"
        end
      | tFix mfix idx =>
          let bodies := map_InP mfix (fun d H => ((BasicAst.string_of_name (d.(dname))), force_lambda (compile d.(dbody)))) in
          Mlet ([Recursive bodies], Mvar (fst (nth (idx) bodies ("", Mstring ""))))
      | tProj (Kernames.mkProjection ind _ nargs) bod with lookup_record_projs Σ ind :=
        { | Some args =>
              let len := List.length args in
              Mfield (int_of_nat (len - 1 - nargs), compile bod)
          | None => Mstring "inductive not found" }
      | tPrim (existT (EPrimitive.primIntModel i)) => Mnum (numconst_Int i)
      | tPrim (existT (EPrimitive.primFloatModel f)) => Mnum (numconst_Float64 f)
      | tPrim (existT (EPrimitive.primStringModel s)) => Mstring (string_of_primstring s)
      | tPrim (existT (EPrimitive.primArrayModel a)) => 
          let default := compile (EPrimitive.array_default a) in
          let values := map_InP (EPrimitive.array_value a) (fun v H => compile v) in
          let arr := compile_array values default in
          Mapply (Mglobal "PArray.of_array", [ arr ; default ])
      | tLazy t => Mlazy (compile t)
      | tForce t => Mforce (compile t)
      | tRel n => Mstring "error: tRel has been translated away"
      | tBox => Mstring "error: tBox has been translated away"
      | tCoFix mfix idx => Mstring "error: tCofix not supported"
      | tEvar _ _ => Mstring "error: tEvar not supported"
      .
    Proof.
      all: try (cbn; lia).
      - subst args. eapply (In_size id size) in H. cbn in *.  
        unfold id in H. change (fun x => size x) with size in H. lia.
      - eapply (In_size snd size) in H. cbn in *.
        lia.
      - eapply (In_size dbody size) in H. cbn in *. lia.
      - eapply (In_size id size) in H. unfold id in *; cbn in *.
        change (fun x => size x) with size in H. lia.
    Qed.
 
End Compile.

Definition compile_constant_decl Σ cb := 
  option_map (compile Σ) cb.(cst_body).

Fixpoint compile_env Σ : list (string * option t) := 
  match Σ with
  | [] => []
  | (x,d) :: Σ => match d with
                  ConstantDecl cb => (Kernames.string_of_kername x, compile_constant_decl Σ cb) :: compile_env Σ
                | _ => compile_env Σ
              end
  end.

Definition compile_program (p : EProgram.eprogram) : Malfunction.program :=
  (compile_env (fst p), compile (fst p) (snd p)).
