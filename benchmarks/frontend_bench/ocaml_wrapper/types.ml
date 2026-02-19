type nat =
| O
| S of nat


let rec of_nat = function
| O -> 0
| S n -> 1 + of_nat n

let rec to_nat = function
| 0 -> O
| n -> S (to_nat (n-1))
