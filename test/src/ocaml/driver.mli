type bool_ = False | True
type 'a list_ = Nil | Cons of 'a * 'a list_
type nat = O | S of nat
type 'a option_ = Some of 'a | None
type ('a, 'b) prod_ = Pair of 'a * 'b
val pp_bool : bool_ -> unit
val pp_list : ('a -> 'b) -> 'a list_ -> unit
val pp_nat : nat -> unit
val pp_option : ('a -> 'b) -> 'a option_ -> unit
val pp_prod : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) prod_ -> unit
