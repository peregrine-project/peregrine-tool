From VerifiedExtraction Require Loader PrimInt63.
From Stdlib Require Import PArray.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument 
  applications, hence typed erasure is required. *)

Verified Extract Constants [ 
  Stdlib.Array.PArray.array erased,
  Stdlib.Array.PArray.make => "Rocq_verified_extraction_ocaml_ffi__Parray.make",
  Stdlib.Array.PArray.get => "Rocq_verified_extraction_ocaml_ffi__Parray.get",
  Stdlib.Array.PArray.default => "Rocq_verified_extraction_ocaml_ffi__Parray.default",
  Stdlib.Array.PArray.set => "Rocq_verified_extraction_ocaml_ffi__Parray.set",
  Stdlib.Array.PArray.length => "Rocq_verified_extraction_ocaml_ffi__Parray.length_int",
  Stdlib.Array.PArray.copy => "Rocq_verified_extraction_ocaml_ffi__Parray.copy" ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].
