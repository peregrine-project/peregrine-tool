(* An unverified pass over the LLVM module that CertiRocq emits. *)
From Stdlib Require Import List String PArith ZArith.
From Vellvm Require Import Syntax.LLVMAst.
Import ListNotations.

(* [tail] on a call whose result the block returns at once (#134).  Not verified:
   Vellvm gives the marker no semantics, so the correctness theorem of the LLVM
   backend does not cover it.  The marker promises that the callee reads nothing of
   the caller's stack frame.  At such a call the emitter has unlinked every
   shadow-stack frame of the caller, and the pass also requires each argument to be
   an [i64] value or the caller's own first parameter, the thread info.  An [i64]
   is safe because the emitter converts no [alloca] address to an integer; the pass
   checks neither property of the emitter. *)
Definition raw_id_eqb (x y : raw_id) : bool :=
  match x, y with
  | Name a, Name b => String.eqb a b
  | Anon a, Anon b | Raw a, Raw b => Z.eqb a b
  | _, _ => false
  end.

Section Tail.
  Context (tinfo : option raw_id).

  Definition tail_arg (a : (typ * exp typ) * list param_attr) : bool :=
    match a with
    | ((TYPE_I sz, _), _) => Pos.eqb sz 64
    | ((TYPE_Pointer None, EXP_Ident (ID_Local x)), _) =>
      match tinfo with
      | Some t => raw_id_eqb x t
      | None => false
      end
    | _ => false
    end.

  Definition tail_code (c : code typ) (r : raw_id) : code typ :=
    match rev c with
    | (IId x, INSTR_Call f args [] obs, md) :: rest =>
      if raw_id_eqb x r then
        if forallb tail_arg args
        then rev ((IId x, INSTR_Call f args [ANN_tail Tail] obs, md) :: rest)
        else c
      else c
    | _ => c
    end.

  Definition tail_block (b : block typ) : block typ :=
    match blk_term b with
    | (_, TERM_Ret (_, EXP_Ident (ID_Local r)), _) =>
      {| blk_id := blk_id b; blk_phis := blk_phis b; blk_code := tail_code (blk_code b) r;
         blk_term := blk_term b; blk_comments := blk_comments b |}
    | _ => b
    end.
End Tail.

Definition tail_tle (e : toplevel_entity typ (block typ * list (block typ)))
  : toplevel_entity typ (block typ * list (block typ)) :=
  match e with
  | TLE_Definition d =>
    let t := match df_args d with x :: _ => Some x | [] => None end in
    let '(b, bs) := df_instrs d in
    TLE_Definition {| df_prototype := df_prototype d; df_args := df_args d;
                      df_instrs := (tail_block t b, map (tail_block t) bs) |}
  | e => e
  end.

(* Examples: a call returned at once is marked; not one with a pointer argument other
   than the thread info, nor one followed by another instruction. *)
Definition tv : raw_id := Name "tinfo".
Definition call (args : list ((typ * exp typ) * list param_attr)) anns :=
  (IId (Raw 5%Z), INSTR_Call (TYPE_I 64%positive, EXP_Ident (ID_Global (Name "f"))) args anns [], @nil (metadata typ)).
Definition blk c := {| blk_id := Anon 1%Z; blk_phis := []; blk_code := c;
                       blk_term := (IVoid 0%Z, TERM_Ret (TYPE_I 64%positive, EXP_Ident (ID_Local (Raw 5%Z))), []);
                       blk_comments := None |}.
Definition ok_args : list ((typ * exp typ) * list param_attr) := [((TYPE_Pointer None, EXP_Ident (ID_Local tv)), []); ((TYPE_I 64%positive, EXP_Ident (ID_Local (Raw 3%Z))), [])].
Example marks : blk_code (tail_block (Some tv) (blk [call ok_args []])) = [call ok_args [ANN_tail Tail]].
Proof. reflexivity. Qed.
Example other_pointer :
  let a : list ((typ * exp typ) * list param_attr) := [((TYPE_Pointer None, EXP_Ident (ID_Local (Raw 9%Z))), [])] in
  blk_code (tail_block (Some tv) (blk [call a []])) = [call a []].
Proof. reflexivity. Qed.
Example not_last :
  let st := (IVoid 1%Z, INSTR_Comment "x", @nil (metadata typ)) in
  blk_code (tail_block (Some tv) (blk [call ok_args []; st])) = [call ok_args []; st].
Proof. reflexivity. Qed.
