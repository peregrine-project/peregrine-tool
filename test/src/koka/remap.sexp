; Attributes for the Remap test on the Koka backend (see doc/format.md): both
; constants become the identity on any, so the test computes 3 only if the axiom is
; defined and the body of shadowed is not used.
; The postulate TODO of agda/Postulates is only applied to the erased type of its
; result, and the result is never called: it throws, so that its result has any
; type, as the typed Koka backend needs.
(attributes_config
  ()
  ((((MPfile ("Remap" "Tests" "Peregrine")) "ext_id") (remapped_constant None 1 false false "fn(x) x"))
   (((MPfile ("Remap" "Tests" "Peregrine")) "shadowed") (remapped_constant None 1 false false "fn(x) x"))
   (((MPfile ("Postulates")) "TODO") (remapped_constant None 1 false false "fn(x) throw(\"peregrine: TODO\")")))
  ()
  ()
  ())
