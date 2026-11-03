(* spawn and get of Tasks.v with OCaml threads.  Each axiom first receives the
   erased type argument.  A task is a thread and the cell of its result; the
   unit argument tt is the constant 0. *)
let def_Tasks_spawn = fun (_ : Obj.t) (f : Obj.t) ->
  let r = ref None in
  let th = Thread.create (fun () -> r := Some ((Obj.magic f : Obj.t -> Obj.t) (Obj.repr 0))) () in
  Obj.repr (th, r)

let def_Tasks_get = fun (_ : Obj.t) (t : Obj.t) ->
  let (th, r) = (Obj.obj t : Thread.t * Obj.t option ref) in
  Thread.join th;
  match !r with Some v -> v | None -> failwith "task raised an exception"
