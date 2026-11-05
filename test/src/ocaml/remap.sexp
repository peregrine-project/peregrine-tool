; Attributes for the Remap test on the OCaml backend (see doc/format.md): both
; constants become Fun.id, so the test computes 3 only if the axiom is
; defined and the body of shadowed is not used.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "Fun.id"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "Fun.id")))
  ()
  ()
  ())
