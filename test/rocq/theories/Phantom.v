(* An inductive with a phantom type parameter. Only the untyped source is
   tested: the typed Rust backend keeps the parameter, and rustc cannot infer
   it at the constructor's PhantomData argument. *)

Inductive Proxy (A : Type) : Type := proxy : Proxy A.

Definition fromProxy {A} (p : Proxy A) : nat := match p with proxy _ => 1 end.

Definition test : nat := fromProxy (proxy nat).
