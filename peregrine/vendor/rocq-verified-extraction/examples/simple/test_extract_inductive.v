From VerifiedExtraction Require Import Extraction.
From MetaRocq.Template Require Import All.
From Stdlib Require Import String.

Set Verified Extraction Build Directory "_build".

Verified Extract Inductives [
  bool => "bool" [ 1 0 ]
].

Definition coq_true := true.
Definition coq_false := false.
(* Set Debug "verified-extraction". *)
Verified Extraction coq_true.
Verified Extraction coq_false.
Verified Extraction andb.

Verified Extract Inductives [
  option => "option" [ 1 0 ] (* This makes switches look at none cases before some *)
].

Definition test_get := (@option_get nat 0%nat None).
Verified Extraction test_get.


