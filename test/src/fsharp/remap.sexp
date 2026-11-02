; Pipeline configuration for the Remap test on the F# backend (see doc/format.md):
; both constants become the identity on obj, so the test computes 3 only if the
; axiom is defined and the body of shadowed is not used.
(config
  (FSharp (fsharp_config None None))
  None
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "fun (x : obj) -> x"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "fun (x : obj) -> x")))
  ()
  ()
  ())
