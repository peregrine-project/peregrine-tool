From Malfunction.Plugin Require Loader PrimInt63.
From Corelib Require Import PrimString.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument 
  applications, hence typed erasure is required. *)

Verified Extract Constants [ 
  Corelib.Strings.PrimString.string erased,
  Corelib.Strings.PrimString.make => "Rocq_verified_extraction_ocaml_ffi__Pstring.make",
  Corelib.Strings.PrimString.length => "Rocq_verified_extraction_ocaml_ffi__Pstring.length",
  Corelib.Strings.PrimString.get => "Rocq_verified_extraction_ocaml_ffi__Pstring.get",
  Corelib.Strings.PrimString.sub => "Rocq_verified_extraction_ocaml_ffi__Pstring.sub",
  Corelib.Strings.PrimString.cat => "Rocq_verified_extraction_ocaml_ffi__Pstring.cat",
  Corelib.Strings.PrimString.compare => "Rocq_verified_extraction_ocaml_ffi__Pstring.compare" ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].
