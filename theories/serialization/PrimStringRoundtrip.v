(** * Round trip between primitive strings and bytestrings

    Replaces the former axioms [prim_string_ser_complete] / [prim_string_ser_sound]
    (the latter was inconsistent with [PrimStringAxioms]: it claimed every bytestring,
    of any length, is the image of a primitive string). *)

From Stdlib Require Import List ZArith Lia Strings.Byte.
From Stdlib Require Import Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import SerializePrimitives DeserializePrimitives.

Import ListNotations.

Lemma char63_valid_bound c : char63_valid c -> (0 <= Uint63Axioms.to_Z c < 256)%Z.
Proof.
  unfold char63_valid. intros H. rewrite <- H, land_spec'.
  change (Uint63Axioms.to_Z 255%uint63) with (Z.ones 8).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma to_Z_char63_of_byte b : Uint63Axioms.to_Z (char63_of_byte b) = Z.of_N (Byte.to_N b).
Proof.
  unfold char63_of_byte. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (Byte.to_N_bounded b).
  assert (255 < wB)%Z by (vm_compute; reflexivity). lia.
Qed.

Lemma char63_of_byte_of_char63 c : char63_valid c -> char63_of_byte (byte_of_char63 c) = c.
Proof.
  intros Hc. apply char63_valid_bound in Hc.
  unfold byte_of_char63. destruct (Byte.of_N (Z.to_N (Uint63Axioms.to_Z c))) eqn:E.
  - apply Byte.to_of_N in E. apply to_Z_inj.
    rewrite to_Z_char63_of_byte, E, Z2N.id by lia. reflexivity.
  - exfalso. apply Byte.of_N_None_iff in E. lia.
Qed.

Lemma byte_of_char63_of_byte b : byte_of_char63 (char63_of_byte b) = b.
Proof.
  unfold byte_of_char63. rewrite to_Z_char63_of_byte, N2Z.id, Byte.of_to_N. reflexivity.
Qed.

Lemma char63_of_byte_valid b : char63_valid (char63_of_byte b).
Proof.
  unfold char63_valid. apply to_Z_inj. rewrite land_spec', to_Z_char63_of_byte.
  change (Uint63Axioms.to_Z 255%uint63) with (Z.ones 8).
  rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (Byte.to_N_bounded b). change (2 ^ 8)%Z with 256%Z. lia.
Qed.

Lemma to_list_of_list (l : list char63) :
  Datatypes.length l <= to_nat max_length -> Forall char63_valid l ->
  to_list (of_list l) = l.
Proof.
  induction l as [|c l IH]; intros Hlen Hv.
  - cbn [of_list]. pose proof (length_spec ""%pstring) as H.
    destruct (to_list ""%pstring); [reflexivity|]. cbn in H. discriminate.
  - inversion Hv as [|? ? Hc Hl]; subst. cbn [of_list Datatypes.length] in *.
    rewrite cat_spec, make_spec, IH by (auto; lia).
    change (to_nat 1%uint63) with 1.
    replace (Nat.min 1 (to_nat max_length)) with 1 by lia.
    unfold char63_valid in Hc. rewrite Hc. cbn [repeat app].
    apply firstn_all2. cbn. lia.
Qed.

Lemma bs_length_parse (l : list byte) : String.length (String.parse l) = Datatypes.length l.
Proof. induction l; cbn; auto. Qed.

Lemma bs_print_parse (l : list byte) : String.print (String.parse l) = l.
Proof. induction l; cbn; f_equal; auto. Qed.

Lemma bs_length_print (s : string) : Datatypes.length (String.print s) = String.length s.
Proof. induction s; cbn; auto. Qed.

Lemma max_length_nonneg : (0 <= Uint63Axioms.to_Z max_length)%Z.
Proof. apply to_Z_bounded. Qed.

Theorem prim_string_of_string_of_prim_string (x : PrimString.string) :
  prim_string_of_string (string_of_prim_string x) = Some x.
Proof.
  unfold prim_string_of_string, string_of_prim_string.
  rewrite bs_length_parse, bs_print_parse, length_map, map_map.
  pose proof (to_list_length x) as Hlen. pose proof max_length_nonneg.
  apply Nat2Z.inj_le in Hlen. rewrite Z2Nat.id in Hlen by exact H.
  rewrite (proj2 (Z.leb_le _ _)) by exact Hlen.
  f_equal. rewrite (map_ext_in _ (fun c => c)).
  - rewrite map_id. apply of_to_list.
  - intros c Hin. apply char63_of_byte_of_char63.
    exact (proj1 (Forall_forall _ _) (to_list_char63_valid x) c Hin).
Qed.

Theorem string_of_prim_string_of_string (s : string) (x : PrimString.string) :
  prim_string_of_string s = Some x -> string_of_prim_string x = s.
Proof.
  unfold prim_string_of_string.
  destruct (Z.of_nat (String.length s) <=? Uint63Axioms.to_Z max_length)%Z eqn:Hle;
    [apply Z.leb_le in Hle|discriminate].
  intros [= <-]. unfold string_of_prim_string.
  rewrite to_list_of_list.
  - rewrite map_map, (map_ext _ _ byte_of_char63_of_byte), map_id.
    clear Hle. induction s as [|b s IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
  - rewrite length_map, bs_length_print. lia.
  - apply Forall_forall. intros c Hin. apply in_map_iff in Hin as (b & <- & _).
    apply char63_of_byte_valid.
Qed.
