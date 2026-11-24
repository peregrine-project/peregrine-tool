# Extraction frontend for Rocq 9.2

This branch builds only Peregrine's frontend, the Rocq plugin that erases a
Rocq program and writes its λ□ AST (`.ast`), for Rocq 9.2. The backends
(`peregrine` executable, `main.exe`) are built from the main branches, which
need Rocq 9.1. Changes against commit 13c701b of branch `numeral-literals`:

- `_CoqProject` lists the theories the plugin needs (no backends) and turns
  off the native compiler, which the typed-extraction packages may lack.
- `theories/Config.v`: verified extraction (Malfunction) has no Rocq 9.2
  release, so the program type of the OCaml backend is `unit`.
- `plugin/src/g_peregrine.mlg`: MetaRocq does not quote sort polymorphism;
  the quality variables of sort-polymorphic library constants met inside
  opaque proofs are dropped, and only their universe levels are quoted.
- `plugin/src/quoter_relevant.ml` (added to `peregrine_plugin.mlpack` and
  `_PluginProject`).

Build, in an opam switch with Rocq 9.2, `rocq-metarocq-erasure-plugin`
1.5.1+9.2, `rocq-ceres-bytestring` 1.0.0 and the packages of
https://github.com/peregrine-project/rocq-typed-extraction at branch
`rocq-9.2-rust-fixes` (commit 5f3c64b):

    rocq makefile -f _CoqProject -o RocqMakefile && make -f RocqMakefile
    make -C plugin

A program then extracts with `-Q theories Peregrine -Q plugin/theories
Peregrine.Plugin` and a findlib directory holding `rocq-peregrine/META`
(`plugin/src/META.rocq-peregrine`) on `OCAMLPATH`.
