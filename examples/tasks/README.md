# Tasks

`Tasks.v` declares `spawn : (unit -> A) -> task A` and `get : task A -> A` as
axioms, with the meaning `get (spawn f) = f tt`, and computes `fib 20 + fib 21`
with two tasks. The axioms are realized per backend:

| Backend | Realization | Runs the tasks |
|---|---|---|
| OCaml | `ocaml/axioms.ml`: a task is a `Thread.t` and the cell of its result | concurrently; on OCaml 4 one thread runs at a time |
| Lean | `lean/remap.sexp`: `spawn` is `Task.spawn` and `get` is `Task.get` | in parallel, on Lean's thread pool |

Each axiom receives the erased type argument first. `make check` builds both
programs and runs them; each prints `17711`. `make check-ocaml` needs no Lean.

A task must not perform IO through the operations of `../io`: the IO
interpreter sequences the operations of one program, and two tasks would run
their operations in no fixed order.
