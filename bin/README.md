# Peregrine CLI

This directory holds the sources for the Peregrine CLI written in OCaml.
It is a wrapper around the extracted Rocq sources of the Peregrine middle-end.

* [main.ml](main.ml): Defines the CLI
* [compile.ml](compile.ml): Bindings for the extracted Rocq code
* [frontend.ml](frontend.ml): Runs the Rocq, Agda and Lean frontends on a source file
* [common.ml](common.ml): Utilities and type definitions
