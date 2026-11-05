; Attributes for the Remap test on the Rust backend (see doc/format.md): both
; constants become the identity, so the test computes 3 only if the axiom is
; defined and the body of shadowed is not used. The identity is generic, as nat
; is a reference to Corelib_Init_Datatypes_nat with the rust verb, and i64
; with rust-i64.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "fn ##name##<T>(&'a self, x: T) -> T { x }"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "fn ##name##<T>(&'a self, x: T) -> T { x }")))
  ()
  ()
  ())
