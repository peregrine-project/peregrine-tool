From VerifiedExtraction
  Require Import Extraction.

Definition function_or_nat
  : forall (b:bool), if b then bool -> bool else nat :=
  fun b =>
    match b with
    | true => fun x => x
    | false => S O
    end.

Definition function := function_or_nat true.

Verified Extraction
  function.
MetaRocq Run Print mli function.
(* val function : bool -> bool *)

Extraction function_or_nat.

Definition apply_function_or_nat : forall b : bool, (if b then bool -> bool else nat) -> bool :=
  fun b => match b with true => fun f => f true | false => fun _ => false end.

Definition assumes_purity : (unit -> bool) -> bool :=
  fun f => apply_function_or_nat (f tt) (function_or_nat (f tt)).

Require Import Extraction.
Recursive Extraction assumes_purity.

MetaRocq Run Print mli assumes_purity.
(* val assumes_purity : (unit -> bool) (* higher-order functions are not safe to extract *)  -> bool *)
