; C remaps of the SEIO* operations (Runtime.v) to runtime_prims.c
(config
  (C (certirocq_config None None None None None None))
  None
  ()
  ((((MPfile ("Runtime")) "io_read") (remapped_constant (Some "runtime_prims.h") 1 true false "io_read"))
   (((MPfile ("Runtime")) "io_write") (remapped_constant (Some "runtime_prims.h") 1 true false "io_write"))
   (((MPfile ("Runtime")) "io_open") (remapped_constant (Some "runtime_prims.h") 1 true false "io_open"))
   (((MPfile ("Runtime")) "io_close") (remapped_constant (Some "runtime_prims.h") 1 true false "io_close")))
  ()
  ()
  ())
