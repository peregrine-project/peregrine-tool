From VerifiedExtraction Require Loader.
From Corelib.Floats Require Import PrimFloat.

Verified Extract Constants [ 
  Corelib.Floats.PrimFloat.float erased,
  Corelib.Floats.PrimFloat.compare => "Rocq_verified_extraction_ocaml_ffi__Float64.compare",
  Corelib.Floats.PrimFloat.eqb => "Rocq_verified_extraction_ocaml_ffi__Float64.equal",
  Corelib.Floats.PrimFloat.ltb => "Rocq_verified_extraction_ocaml_ffi__Float64.lt",
  Corelib.Floats.PrimFloat.leb => "Rocq_verified_extraction_ocaml_ffi__Float64.le",
  Corelib.Floats.PrimFloat.frshiftexp => "Rocq_verified_extraction_ocaml_ffi__Float64.frshiftexp",
  Corelib.Floats.PrimFloat.ldshiftexp => "Rocq_verified_extraction_ocaml_ffi__Float64.ldshiftexp",
  Corelib.Floats.PrimFloat.normfr_mantissa => "Rocq_verified_extraction_ocaml_ffi__Float64.normfr_mantissa",
  Corelib.Floats.PrimFloat.classify => "Rocq_verified_extraction_ocaml_ffi__Float64.classify",
  Corelib.Floats.PrimFloat.abs => "Rocq_verified_extraction_ocaml_ffi__Float64.abs",
  Corelib.Floats.PrimFloat.sqrt => "Rocq_verified_extraction_ocaml_ffi__Float64.sqrt",
  Corelib.Floats.PrimFloat.opp => "Rocq_verified_extraction_ocaml_ffi__Float64.opp",
  Corelib.Floats.PrimFloat.div => "Rocq_verified_extraction_ocaml_ffi__Float64.div",
  Corelib.Floats.PrimFloat.mul => "Rocq_verified_extraction_ocaml_ffi__Float64.mul",
  Corelib.Floats.PrimFloat.add => "Rocq_verified_extraction_ocaml_ffi__Float64.add",
  Corelib.Floats.PrimFloat.sub => "Rocq_verified_extraction_ocaml_ffi__Float64.sub",
  Corelib.Floats.PrimFloat.of_uint63 => "Rocq_verified_extraction_ocaml_ffi__Float64.of_uint63",
  Corelib.Floats.PrimFloat.next_up => "Rocq_verified_extraction_ocaml_ffi__Float64.next_up",
  Corelib.Floats.PrimFloat.next_down => "Rocq_verified_extraction_ocaml_ffi__Float64.next_down" ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].
