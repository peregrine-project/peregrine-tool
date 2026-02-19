From VerifiedExtraction Require Loader.
From Corelib Require Int63.PrimInt63.

(** Primitive ints *)
Verified Extract Constants [
  Corelib.Numbers.Cyclic.Int63.PrimInt63.int erased,
  Corelib.Numbers.Cyclic.Int63.PrimInt63.add => "Rocq_verified_extraction_ocaml_ffi__Uint63.add",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.sub => "Rocq_verified_extraction_ocaml_ffi__Uint63.sub", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mul => "Rocq_verified_extraction_ocaml_ffi__Uint63.mul", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.div => "Rocq_verified_extraction_ocaml_ffi__Uint63.div", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mod => "Rocq_verified_extraction_ocaml_ffi__Uint63.rem", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_sl", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_sr", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.land => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_and",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_xor",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lor => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_or",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.asr => "Rocq_verified_extraction_ocaml_ffi__Uint63.a_sr",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.head0 => "Rocq_verified_extraction_ocaml_ffi__Uint63.head0", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.tail0 => "Rocq_verified_extraction_ocaml_ffi__Uint63.tail0", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb => "Rocq_verified_extraction_ocaml_ffi__Uint63.equal",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.compare => "Rocq_verified_extraction_ocaml_ffi__Uint63.compare", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.compares => "Rocq_verified_extraction_ocaml_ffi__Uint63.compares", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addc => "Rocq_verified_extraction_ocaml_ffi__Uint63.addc", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "Rocq_verified_extraction_ocaml_ffi__Uint63.addcarryc", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.subc => "Rocq_verified_extraction_ocaml_ffi__Uint63.subc",
  Corelib.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "Rocq_verified_extraction_ocaml_ffi__Uint63.subcarryc", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc => "Rocq_verified_extraction_ocaml_ffi__Uint63.mulc", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.divs => "Rocq_verified_extraction_ocaml_ffi__Uint63.divs", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.mods => "Rocq_verified_extraction_ocaml_ffi__Uint63.rems", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "Rocq_verified_extraction_ocaml_ffi__Uint63.div21", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl => "Rocq_verified_extraction_ocaml_ffi__Uint63.diveucl", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "Rocq_verified_extraction_ocaml_ffi__Uint63.addmuldiv", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.leb => "Rocq_verified_extraction_ocaml_ffi__Uint63.le", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb => "Rocq_verified_extraction_ocaml_ffi__Uint63.lt", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb => "Rocq_verified_extraction_ocaml_ffi__Uint63.lts", 
  Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb => "Rocq_verified_extraction_ocaml_ffi__Uint63.les"
]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].
