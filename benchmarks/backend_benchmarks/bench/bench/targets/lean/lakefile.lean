import Lake
open Lake DSL

package benchmarks where
  moreLeanArgs := #["-DautoImplicit=false"]

@[default_target]
lean_exe binary_trees where
  root := `BinaryTrees

lean_exe fannkuch where
  root := `Fannkuch

lean_exe pidigits where
  root := `Pidigits

lean_exe nqueens where
  root := `NQueens

lean_exe ackermann where
  root := `Ackermann

lean_exe tak where
  root := `Tak

lean_exe quicksort where
  root := `Quicksort

lean_exe sieve where
  root := `Sieve

lean_exe treesort where
  root := `Treesort

lean_exe symbolic_diff where
  root := `SymbolicDiff

lean_exe lambda_interp where
  root := `LambdaInterp
