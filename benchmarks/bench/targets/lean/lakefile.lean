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
