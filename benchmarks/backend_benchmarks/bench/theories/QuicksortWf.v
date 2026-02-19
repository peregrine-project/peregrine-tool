(** * Quicksort Benchmark (Well-founded recursion version)

    Functional quicksort using well-founded recursion on list length.
    No explicit fuel - termination is proven via measure.
*)

From Stdlib Require Import List ZArith Lia.
From Stdlib.Program Require Import Wf.
Import ListNotations.

Open Scope Z_scope.

(** Partition a list into elements < pivot and elements >= pivot *)
Fixpoint partition (pivot : Z) (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | x :: xs =>
      let (lo, hi) := partition pivot xs in
      if x <? pivot then (x :: lo, hi) else (lo, x :: hi)
  end.

(** Partition preserves total length *)
Lemma partition_length : forall pivot l lo hi,
  partition pivot l = (lo, hi) ->
  (length lo + length hi = length l)%nat.
Proof.
  intros pivot l. induction l as [|x xs IH]; intros lo hi H.
  - simpl in H. injection H as <- <-. reflexivity.
  - simpl in H.
    destruct (partition pivot xs) as [lo' hi'] eqn:Heq.
    destruct (x <? pivot); injection H as <- <-; simpl;
    specialize (IH lo' hi' eq_refl); lia.
Qed.

(** Partition results are no larger than input *)
Lemma partition_lo_le : forall pivot l lo hi,
  partition pivot l = (lo, hi) -> (length lo <= length l)%nat.
Proof.
  intros. pose proof (partition_length _ _ _ _ H). lia.
Qed.

Lemma partition_hi_le : forall pivot l lo hi,
  partition pivot l = (lo, hi) -> (length hi <= length l)%nat.
Proof.
  intros. pose proof (partition_length _ _ _ _ H). lia.
Qed.

(** Quicksort using Function with measure *)
From Stdlib Require Import Recdef.

Function quicksort (l : list Z) {measure length l} : list Z :=
  match l with
  | [] => []
  | [x] => [x]
  | pivot :: rest =>
      let (lo, hi) := partition pivot rest in
      quicksort lo ++ [pivot] ++ quicksort hi
  end.
Proof.
  all: intros; simpl.
  - (* hi case *)
    pose proof (partition_hi_le pivot (z :: l0) lo hi teq1). simpl in H. lia.
  - (* lo case *)
    pose proof (partition_lo_le pivot (z :: l0) lo hi teq1). simpl in H. lia.
Defined.

(** Generate a pseudo-random list for testing using LCG *)
Fixpoint make_list_aux (seed : Z) (fuel : nat) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      let next := (seed * 1103515245 + 12345) mod 2147483648 in
      make_list_aux next fuel' (next :: acc)
  end.

Definition make_list (n : nat) : list Z :=
  make_list_aux 42 n [].

(** Check if a list is sorted *)
Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as rest) => (x <=? y) && is_sorted rest
  end.

(** Length as Z *)
Fixpoint length_Z {A : Type} (l : list A) : Z :=
  match l with
  | [] => 0
  | _ :: xs => 1 + length_Z xs
  end.

(** Benchmark: sort n random elements, return length if sorted *)
Definition quicksort_bench_wf (n : nat) : Z :=
  let l := make_list n in
  let sorted := quicksort l in
  if is_sorted sorted then length_Z sorted else 0.

(** Benchmarks *)
Definition quicksort_wf_10 : Z := quicksort_bench_wf 10.
Definition quicksort_wf_100 : Z := quicksort_bench_wf 100.
Definition quicksort_wf_500 : Z := quicksort_bench_wf 500.
Definition quicksort_wf_1000 : Z := quicksort_bench_wf 1000.
