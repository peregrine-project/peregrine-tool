; Pipeline configuration for the Rust backend tests (see doc/format.md).
;
; rust_preamble_top and rust_default_attributes make the generated types
; serializable, so that the test driver can print the result as an
; S-expression.
;
; dearg_ctors and dearg_consts are off: they select the *trimming* of the
; dearging masks, and the expected outputs in tests.ts are written for
; untrimmed masks.
(config
  (Rust (rust_config
    (Some "use lexpr::{to_string}; use serde_derive::{Serialize}; use serde_lexpr::{to_value};")
    None None None None None
    (Some "#[derive(Debug, Clone, Serialize)]")))
  (Some (erasure_phases None None None None None (Some false) (Some false)))
  () () () () ())
