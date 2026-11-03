(** Echo: read standard input to its end and write it twice to standard
    output.  The program is a free-monad value over the SEIO* operations of
    [Runtime]; [interp] performs each operation before it applies the
    continuation to the result, so evaluation keeps their order. *)
From Peregrine.Plugin Require Import Loader.
From Stdlib Require Import PrimString.
Require Runtime.

Inductive op :=
| Read (fd : nat)
| Write (fd : nat) (s : string)
| Open (name : string)
| Close (fd : nat).

Inductive resp :=
| RStr (r : string + unit)
| RUnit (r : unit + unit)
| RNat (r : nat + unit).

Inductive free (A : Type) : Type :=
| Pure (a : A)
| Op (o : op) (k : resp -> free A).
Arguments Pure {A} a.
Arguments Op {A} o k.

Definition perform (o : op) : resp :=
  match o with
  | Read fd => RStr (Runtime.io_read fd)
  | Write fd s => RUnit (Runtime.io_write (fd, s))
  | Open name => RNat (Runtime.io_open name)
  | Close fd => RUnit (Runtime.io_close fd)
  end.

Fixpoint interp {A} (m : free A) : A :=
  match m with
  | Pure a => a
  | Op o k => interp (k (perform o))
  end.

Definition write (fd : nat) (s : string) (next : free unit) : free unit :=
  Op (Write fd s) (fun _ => next).

Definition newline : string := "
"%pstring.

Definition echo : free unit :=
  Op (Read 0) (fun r =>
    match r with
    | RStr (inl input) => write 1 input (write 1 input (Pure tt))
    | _ => write 2 "no input"%pstring (write 2 newline (Pure tt))
    end).

Definition main : unit := interp echo.

Peregrine Extract "../build/Echo.ast" main.
