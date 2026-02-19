From VerifiedExtraction Require Import Extraction.

Verified Extraction (plus, mult).

Verified Extraction (1 + 2).
MetaRocq Run Print mli (1 + 2).

Verified Extraction (plus, mult) "multiple.mlf".
MetaRocq Run Print mli (plus, mult).
