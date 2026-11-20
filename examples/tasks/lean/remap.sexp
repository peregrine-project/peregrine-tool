; spawn and get of Tasks.v as Lean's Task.  Each receives the erased type argument.
(config
  (Lean (lean_config None None))
  None
  ()
  ((((MPfile ("Tasks")) "spawn") (remapped_constant None 2 false false "fun (_ : Obj) (f : Obj) => Peregrine.reflect (Task.spawn (fun _ => Peregrine.apply f (Peregrine.reflect ())))"))
   (((MPfile ("Tasks")) "get") (remapped_constant None 2 false false "fun (_ : Obj) (t : Obj) => (Peregrine.cast t : Task Obj).get")))
  ()
  ()
  ())
