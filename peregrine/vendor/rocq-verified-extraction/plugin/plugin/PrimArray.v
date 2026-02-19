From Malfunction.Plugin Require Loader PrimInt63.
From Corelib Require Import PrimArray.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument 
  applications, hence typed erasure is required. *)

Verified Extract Constants [ 
  Corelib.Array.PrimArray.array erased,
  Corelib.Array.PrimArray.make => "Rocq_verified_extraction_ocaml_ffi__Parray.make",
  Corelib.Array.PrimArray.get => "Rocq_verified_extraction_ocaml_ffi__Parray.get",
  Corelib.Array.PrimArray.default => "Rocq_verified_extraction_ocaml_ffi__Parray.default",
  Corelib.Array.PrimArray.set => "Rocq_verified_extraction_ocaml_ffi__Parray.set",
  Corelib.Array.PrimArray.length => "Rocq_verified_extraction_ocaml_ffi__Parray.length_int",
  Corelib.Array.PrimArray.copy => "Rocq_verified_extraction_ocaml_ffi__Parray.copy" ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].
