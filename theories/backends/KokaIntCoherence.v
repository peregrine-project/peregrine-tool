(** The operations of [KokaIntRemaps] agree with those of [Nat], for a model of Koka's
    [int] as [Z] on non-negative values.  The strings in [KokaIntRemaps] are not connected
    to these definitions, and the Koka compiler is trusted: this file checks the
    arithmetic each string writes, including what it does on a zero divisor and on a
    subtraction below zero.  Koka's [/] and [%] are modelled by [Z.div] and [Z.modulo],
    which agree with truncating division on the non-negative values that occur here. *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

Definition koka_sub (a b : Z) : Z := if a <? b then 0 else a - b.
Definition koka_max (a b : Z) : Z := if a <? b then b else a.
Definition koka_min (a b : Z) : Z := if a <? b then a else b.
Definition koka_div (a b : Z) : Z := if b =? 0 then 0 else a / b.
Definition koka_mod (a b : Z) : Z := if b =? 0 then a else a mod b.

Section Coherence.
  Variables a b : nat.

  Lemma koka_add_correct : Z.of_nat a + Z.of_nat b = Z.of_nat (a + b).
  Proof. lia. Qed.

  Lemma koka_mul_correct : Z.of_nat a * Z.of_nat b = Z.of_nat (a * b).
  Proof. lia. Qed.

  Lemma koka_sub_correct : koka_sub (Z.of_nat a) (Z.of_nat b) = Z.of_nat (a - b).
  Proof.
    unfold koka_sub. destruct (Z.ltb_spec (Z.of_nat a) (Z.of_nat b)); lia.
  Qed.

  Lemma koka_max_correct : koka_max (Z.of_nat a) (Z.of_nat b) = Z.of_nat (Nat.max a b).
  Proof.
    unfold koka_max. destruct (Z.ltb_spec (Z.of_nat a) (Z.of_nat b)); lia.
  Qed.

  Lemma koka_min_correct : koka_min (Z.of_nat a) (Z.of_nat b) = Z.of_nat (Nat.min a b).
  Proof.
    unfold koka_min. destruct (Z.ltb_spec (Z.of_nat a) (Z.of_nat b)); lia.
  Qed.

  Lemma koka_div_correct : koka_div (Z.of_nat a) (Z.of_nat b) = Z.of_nat (Nat.div a b).
  Proof.
    unfold koka_div. destruct b as [|b'].
    - reflexivity.
    - rewrite Nat2Z.inj_div. destruct (Z.eqb_spec (Z.of_nat (S b')) 0); [lia|reflexivity].
  Qed.

  Lemma koka_mod_correct : koka_mod (Z.of_nat a) (Z.of_nat b) = Z.of_nat (Nat.modulo a b).
  Proof.
    unfold koka_mod. destruct b as [|b'].
    - reflexivity.
    - rewrite Nat2Z.inj_mod. destruct (Z.eqb_spec (Z.of_nat (S b')) 0); [lia|reflexivity].
  Qed.

  Lemma koka_pow_correct : Z.pow (Z.of_nat a) (Z.of_nat b) = Z.of_nat (Nat.pow a b).
  Proof. rewrite Nat2Z.inj_pow. reflexivity. Qed.

  Lemma koka_eqb_correct : (Z.of_nat a =? Z.of_nat b) = Nat.eqb a b.
  Proof.
    destruct (Z.eqb_spec (Z.of_nat a) (Z.of_nat b)), (Nat.eqb_spec a b); lia.
  Qed.

  Lemma koka_leb_correct : (Z.of_nat a <=? Z.of_nat b) = Nat.leb a b.
  Proof.
    destruct (Z.leb_spec (Z.of_nat a) (Z.of_nat b)), (Nat.leb_spec a b); lia.
  Qed.

  Lemma koka_ltb_correct : (Z.of_nat a <? Z.of_nat b) = Nat.ltb a b.
  Proof.
    destruct (Z.ltb_spec (Z.of_nat a) (Z.of_nat b)), (Nat.ltb_spec a b); lia.
  Qed.
End Coherence.
