type ('a, 'b) prod =
| Pair of 'a * 'b

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

val color : unit -> (z, z) prod
