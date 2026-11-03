import Gen

open Peregrine in
unsafe inductive PNat : Type where
  | zero
  | succ (n : Obj)

open Peregrine in
unsafe def natOf (o : Obj) (acc : Nat) : Nat :=
  match (Peregrine.cast o : PNat) with
  | .zero => acc
  | .succ n => natOf n (acc + 1)

unsafe def main : IO Unit := IO.println (natOf Generated.Tasks_main.get 0)
