(* An inductive with a phantom type parameter. The typed Rust backend keeps
   the parameter, and rustc cannot infer it at the constructor's PhantomData
   argument (#127; fixed by peregrine-project/rocq-typed-extraction#19). *)

Inductive Proxy (A : Type) : Type := proxy : Proxy A.

Definition fromProxy {A} (p : Proxy A) : nat := match p with proxy _ => 1 end.

Definition test : nat := fromProxy (proxy nat).
