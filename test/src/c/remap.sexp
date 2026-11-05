; Attributes for the Remap test on the C and LLVM backends (see doc/format.md):
; both constants become remap_id, the identity of remap.h and remap.c, so the
; test computes 3 only if the axiom is defined and the body of shadowed is not
; used.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant (Some "remap.h") 1 false false "remap_id"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant (Some "remap.h") 1 false false "remap_id")))
  ()
  ()
  ())
