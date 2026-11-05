; Attributes for the Remap test on the Rust backend (see doc/format.md): both
; constants become the identity on nat, so the test computes 3 only if the
; axiom is defined and the body of shadowed is not used.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "fn ##name##(&'a self, x: &'a Corelib_Init_Datatypes_nat<'a>) -> &'a Corelib_Init_Datatypes_nat<'a> { x }"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "fn ##name##(&'a self, x: &'a Corelib_Init_Datatypes_nat<'a>) -> &'a Corelib_Init_Datatypes_nat<'a> { x }")))
  ()
  ()
  ())
