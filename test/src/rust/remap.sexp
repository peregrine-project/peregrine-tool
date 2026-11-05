; Attributes for the Remap test on the Rust backend (see doc/format.md): both
; constants become the identity, so the test computes 3 only if the axiom is
; defined and the body of shadowed is not used. The identity is generic, as nat
; is a reference to Corelib_Init_Datatypes_nat with the rust verb, and i64
; with rust-i64.
; The postulate TODO of agda/Postulates is only reached in a branch that is not
; taken. Dearging removes its one argument, the erased type of its result, so
; its realisation takes none.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "fn ##name##<T>(&'a self, x: T) -> T { x }"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "fn ##name##<T>(&'a self, x: T) -> T { x }"))
   (((MPfile ("Postulates")) "TODO") (remapped_constant None 0 false false "fn ##name##<T>(&'a self) -> T { panic!(\"postulate\") }")))
  ()
  ()
  ())
