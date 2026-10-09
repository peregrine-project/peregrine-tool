; Pipeline configuration for the Elm backend tests (see doc/format.md).
;
; elm_preamble imports what the test driver's main and test functions need.
;
; The backend prints elm_false_elim_def, an expression, at the top level of
; the module, which Elm rejects. Until that is fixed the tests define
; false_rec in the preamble and set elm_false_elim_def to the empty string,
; so a program that eliminates False does not compile with this
; configuration.
;
; dearg_ctors and dearg_consts are off: they select the *trimming* of the
; dearging masks, and the expected outputs in tests.ts are written for
; untrimmed masks.
(config
  (Elm (elm_config
    (Some "import Test\nimport Html\nimport Expect exposing (Expectation)\n\nfalse_rec : () -> a\nfalse_rec _ = false_rec ()")
    None None None None
    (Some "")
    None))
  (Some (erasure_phases None None None None None (Some false) (Some false)))
  () () () () ())
