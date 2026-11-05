# Using Peregrine

This page lists every command and option of the `peregrine` command. `peregrine --help` and `peregrine COMMAND --help` show the same information.

* [Commands](#commands)
* [Input and frontends](#frontends)
* [Common options](#common-options)
* [Middle-end passes](#middle-end-passes)
* [Backend options](#backend-options)
* [Configuration and attribute files](#configuration-and-attribute-files)
* [Exit codes](#exit-codes)
* [Deprecated commands and options](#deprecated-commands-and-options)
* [Examples](#examples)


## Commands

```
peregrine BACKEND INPUT [-o OUTPUT] [OPTIONS]      compile INPUT with BACKEND
peregrine erase INPUT [-o OUTPUT.ast] [OPTIONS]    run only the frontend
peregrine compile INPUT CONFIG_FILE [OPTIONS]      compile with a pipeline configuration file
peregrine ast TYPE INPUT [OPTIONS]                 print an intermediate representation
peregrine validate INPUT [--config FILE]           check the program and a configuration
peregrine help [TOPIC]
```

`INPUT` is a Rocq, Agda or Lean source file, or a $\lambda_\square$ program; see [Input and frontends](#frontends).

### Backend commands

| Command | Output (default name) | Input | Options |
|---------|-----------------------|-------|---------|
| `c` | `INPUT.c` and `INPUT.h` | untyped | [CertiRocq](#certirocq-options-c-wasm-llvm-eval-ast) |
| `wasm` | `INPUT.wasm` | untyped | [CertiRocq](#certirocq-options-c-wasm-llvm-eval-ast) |
| `llvm` (experimental) | `INPUT.ll` | untyped | [CertiRocq](#certirocq-options-c-wasm-llvm-eval-ast) |
| `ocaml` | `INPUT.mlf` | untyped | |
| `cakeml` | `INPUT.cml` | untyped | |
| `rust` | `INPUT.rs` | typed | [`--numbers`](#rust) |
| `elm` | `INPUT.elm` | typed | |
| `lean` | `INPUT.lean` | untyped | |
| `fsharp` (experimental) | `INPUT.fs` | untyped | |
| `koka` (experimental) | `INPUT.kk` | untyped | |
| `eval` | the value, on standard output | untyped | [CertiRocq](#certirocq-options-c-wasm-llvm-eval-ast), [`--fuel`](#eval) |

`INPUT.ext` stands for `INPUT` with its extension replaced (`Prog.v` gives `Prog.c`). `-o` sets the output file. For `c`, the header gets the name of the `-o` file with `.h` in place of its extension. The `.c` file includes the header by its base name, so keep the two in one directory.

Every backend command takes the [frontend options](#frontends), the [common options](#common-options) and the [middle-end pass options](#middle-end-passes).

A typed backend (`rust`, `elm`) given an untyped program first infers its types. If the program cannot be typed this way, peregrine fails with an error that names the offending constant ([backends.md](backends.md#rust)). An untyped backend given a typed program ignores the types.

What each backend produces and what is needed to build and run its output is described in [backends.md](backends.md).

### `erase`
```
peregrine erase INPUT [-o OUTPUT] [--typed] [--entry NAME] [--from FRONTEND] [--frontend-arg ARG]…
```
Runs the frontend and writes the $\lambda_\square$ program to `OUTPUT` (default `INPUT.ast`). It writes typed $\lambda_\square^T$ with `--typed`. For Lean it also writes the attribute file `OUTPUT.inlinings`. `INPUT` must be a source file.

### `compile`
```
peregrine compile INPUT CONFIG_FILE [-o OUTPUT] [--attributes FILES]
```
Compiles with the pipeline configuration in `CONFIG_FILE`, which selects the backend and all its options ([format.md](format.md#configuration)). The middle-end pass flags do not apply: the configuration sets the passes. With a source `INPUT`, the frontend gives typed $\lambda_\square^T$ when the configuration selects Rust, Elm or `AST LambdaBoxTyped`.

### `ast`
```
peregrine ast TYPE INPUT [-o OUTPUT]
```
Runs the middle-end and writes the program it would hand to a backend, by default to `INPUT.ast`. **With a `.ast` input and no `-o`, the output overwrites the input.** `TYPE` is one of:

* `box`: untyped $\lambda_\square$
* `typed`: typed $\lambda_\square^T$, inferring the types of untyped input
* `anf`, `anfc`: CertiRocq's $\lambda_{ANF}$. The $\lambda_{ANF}$ printer is not written yet, so the output is `TODO`.

`ast` takes the CertiRocq options, which apply to `anf` and `anfc`.

### `validate`
```
peregrine validate INPUT [--config FILE] [--attributes FILES]
```
Parses `INPUT` and checks that it is well formed: no undefined or unsorted declarations, closed terms, no constructors in block form, exhaustive cases. It also parses and checks the configuration file and attribute files, if given. This is the quickest way to check the output of a new frontend ([frontends.md](frontends.md#writing-a-new-frontend)).

### `help`
`peregrine help COMMAND` shows the manual of a command. `peregrine help topics` lists the topics.


<a id="frontends"></a>
## Input and frontends

Peregrine picks the frontend from the extension of `INPUT`:

| Extension | Frontend | Tool run by peregrine |
|-----------|----------|------------------------|
| `.v` | Rocq | `rocq compile` |
| `.agda`, `.lagda`, `.lagda.md`, `.lagda.tex`, `.lagda.rst`, `.lagda.org`, `.lagda.typ`, `.lagda.tree` | Agda | `agda2lambox` |
| `.lean` | Lean | `lake env lean` |
| any other | none: `INPUT` is a $\lambda_\square$ program | |

The tool runs in a temporary directory, which is removed afterwards. With `-d` it is kept, and its path is printed. With `-v` the command line of the tool is printed. The output of the tool (warnings, progress) is shown as is.

Peregrine prints on standard error one line for each choice it makes by itself: the frontend picked from the extension, typed or untyped $\lambda_\square$, the Rocq project file and its options, the logical path of a Rocq input (or that it has none), the Lake project, and the Lean inlinings passed as attributes. `-q` hides these lines.

### Frontend options

* `--from FRONTEND`: use `FRONTEND` (`rocq`, `agda`, `lean` or `lambdabox`) whatever the extension.
* `--entry NAME`: the definition to extract. Required for Rocq and Lean. Agda does not accept it: agda2lambox extracts the definitions marked with `{-# COMPILE AGDA2LAMBOX NAME #-}`, and the first of them is the main term.
* `--frontend-arg ARG`: pass `ARG` to the tool. Repeat it for several arguments, and write an argument that starts with `-` as `--frontend-arg=ARG`, e.g. `--frontend-arg=-Q --frontend-arg=theories --frontend-arg=MyLib`.
* `--lean-config TERM`: the configuration of the Lean frontend, a Lean term of type `Erasure.ErasureConfig`, given to `#erase NAME config TERM`, e.g. `--lean-config '{nat := .peano}'`. An error with any other frontend.
* `--keep-ast FILE`: also write the $\lambda_\square$ program of the frontend to `FILE`, and for Lean the attribute file to `FILE.inlinings`.
* `--typed`: ask the frontend for typed $\lambda_\square^T$. Without it, peregrine asks for typed output when the backend needs it (`rust`, `elm`, `ast typed`, or `compile` with such a backend) and the frontend has it (Rocq, Agda). Lean has no typed output: `--typed` with Lean is an error, and the typed backends infer the types of its untyped output.

`--entry`, `--typed`, `--frontend-arg` and `--lean-config` are errors on a $\lambda_\square$ input.

### Rocq

Needs Rocq and the Peregrine plugin, both installed by `opam install rocq-peregrine`.

**Load path.** The load path is that of the `-Q`, `-R` and `-I` options in `--frontend-arg`, written as for `rocq compile`: `--frontend-arg=-Q --frontend-arg=DIR --frontend-arg=Lib`. Relative paths are relative to the current directory. When `--frontend-arg` has none of these options, peregrine looks for the nearest `_RocqProject` or `_CoqProject`, from the directory of `INPUT` upwards (preferring `_RocqProject` in the same directory). It takes the `-Q`, `-R`, `-I` and `-arg` options of that file, with paths relative to the file, and ignores the file lists and other options. It prints the file and the options it took. When these options do not fit, for instance when an `-I` names a plugin directory that is not built, give the load path with `--frontend-arg` instead.

**Names.** When the load path gives `INPUT` a logical path (`theories/Sub/Main.v` under `-Q theories Foo` is `Foo.Sub.Main`), peregrine compiles a copy of `INPUT` that ends with `From Peregrine.Plugin Require Import Loader.` and `Peregrine Extract NAME` (or `Peregrine Extract Typed`), under that logical path, in the temporary directory. The extracted names are then those that `Peregrine Extract` gives inside the project, e.g. `Foo.Sub.Main.main`. Nothing is written to the project. Otherwise (no load path covers `INPUT`, or its name does not end in `.v`), peregrine compiles a driver that `Load`s `INPUT` (or a `.v` copy of it) and then runs `Peregrine Extract`. The driver takes the base name of `INPUT`, so the names are those of a module of that name, e.g. `Main.main`, and peregrine says so.

In both cases `NAME` is resolved at the end of `INPUT`, so it can be any name visible there, qualified or not. In the first case, error positions refer to the copy, which has the same lines as `INPUT`. The modules that `INPUT` requires must already be compiled (`.vo` files in the project, e.g. by its `make`). Peregrine compiles `INPUT` only.

The same extraction is available inside Rocq ([frontends.md](frontends.md#rocq)):
```coq
From Peregrine.Plugin Require Import Loader.
Peregrine Extract "prog.ast" main.
Peregrine Extract Typed "prog_typed.ast" main.
```

### Agda

Needs [agda2lambox](https://github.com/agda/agda2lambox) on the `PATH`. Build it with `cabal install` in a clone of that repository.

Peregrine runs `agda2lambox [--typed] -o TMPDIR ARG… INPUT` in the directory of `INPUT`, which is the project root of a module without a `module` header. Agda finds `.agda-lib` files as usual. Relative paths in `--frontend-arg` (e.g. `--frontend-arg=-i --frontend-arg=lib`) are therefore relative to that directory. Agda writes its interface files (`.agdai`) next to the sources, as it always does.

Mark the definitions to extract in the source:
```agda
test : List Bool
test = cons true (cons false empty)
{-# COMPILE AGDA2LAMBOX test #-}
```
Untyped output needs at least one pragma.

### Lean

Needs [Lean](https://lean-lang.org/install/) (`lake`, through elan) and a Lake project that requires [lean-to-lambdabox](https://github.com/peregrine-project/lean-to-lambdabox), for example in `lakefile.lean`:
```lean
require lean_to_lambdabox from git
  "https://github.com/peregrine-project/lean-to-lambdabox" @ "main"
```
Build the project (`lake build`) before running peregrine, so that LeanToLambdaBox and the modules `INPUT` imports are compiled.

Peregrine finds the Lake project in the nearest directory, from that of `INPUT` upwards, that has a `lakefile.lean` or `lakefile.toml`. It copies `INPUT` to the temporary directory, with `import LeanToLambdaBox` added at the top and `#erase NAME to "…"` at the end. Then it runs `lake env lean ARG… COPY` in the project directory, so relative paths in `--frontend-arg` are relative to that directory. Error positions refer to the copy, which has one more line at the top than `INPUT`.

`#erase` also writes an attribute file listing the constants to inline. Peregrine passes it to the middle-end with the files of `--attributes`.

`#erase` runs with its default configuration (`nat := .machine`) unless `--lean-config` gives another one. With the default, `Nat` literals become machine integers, and the `@[extern]` functions on `Nat` become axioms that the target must implement ([frontends.md](frontends.md#lean)). With `--lean-config '{nat := .peano}'`, `Nat` stays an inductive type.

### $\lambda_\square$ programs

Any frontend can write a $\lambda_\square$ program, as an S-expression file in the format of [format.md](format.md). Whether the program is typed is part of the content (`(Untyped …)` or `(Typed …)`), not of the file name.


## Common options

These options apply to every command.

* `-o FILE`, `--outfile=FILE`: the output file.
* `--attributes=FILE[,FILE…]`: attribute files, merged into the configuration ([format.md](format.md#attribute-files)). The option takes a comma-separated list and cannot be repeated.
* `-q`, `--quiet`: do not print the progress lines (`Compiling:`, `Compiled successfully:`, `Validating AST:`, `AST is valid`).
* `-v`, `--verbose`: print the command line of the frontend tool.
* `-d`, `--debug`: keep the temporary directory of the frontend and print its path.
* `--help`, `--version`


## Middle-end passes

The backend commands (not `compile`, `validate` or `erase`) take these flags, which switch optional passes of the middle-end. Each takes `true` or `false`. Without the flag, the backend's default applies. The defaults are in the tables of [middleend.md](middleend.md#transformation-support-untyped-target-ast). A backend that requires a pass, or cannot run it, ignores the flag.

| Flag | Pass |
|------|------|
| `--betared` | beta reduction |
| `--unboxing` | remove singleton types (inductives with one constructor of one argument) |
| `--dearg-ctors` | remove dead constructor arguments |
| `--dearg-consts` | remove dead constant arguments |
| `--specialize-instances` | specialize functions at the call sites that pass a statically known dictionary (record) value |
| `--cse` | bind closed subterms that occur more than once with a `let` |
| `--lower-cofix` | translate cofixpoints, `lazy` and `force` to fixpoints and thunks |

* `--specialize-instances` and `--cse` are off by default and act only on the untyped targets. The typed pipeline of `rust` and `elm` does not run them. Their correctness rests on axioms ([middleend.md](middleend.md#optional-passes)).
* `--lower-cofix` uses two passes whose evaluation-preservation proofs are admitted. Without it, `c`, `wasm`, `llvm`, `ocaml`, `cakeml` and `eval` reject a program that still has cofixpoints, `lazy` or `force` after the middle-end. `lean`, `fsharp` and `koka` always run these passes.


## Backend options

### CertiRocq options (`c`, `wasm`, `llvm`, `eval`, `ast`)

These set the `certirocq_config` record ([format.md](format.md#c--wasm--llvm-certirocq_config)) that CertiRocq reads.

* `--cps`: use CertiRocq's CPS pipeline instead of the direct one.
* `--c-args=N`: the number of arguments that the generated functions take as C arguments; the rest are passed in an array (default 5).
* `-O N`: CertiRocq's optimization level. 0, the default, disables lambda lifting; 1 and above enable it.
* `--body-name=NAME`: the name of the top-level function (default `body`). The LLVM backend ignores it and always names its entry point `certirocq_main`.

`--prefix` and `--anf-conf` are accepted but [deprecated](#deprecated-commands-and-options): nothing reads them.

### Rust

`--numbers=NUMBERS` selects the representation of `nat`, `positive`, `N` and `Z`:

| `NUMBERS` | Representation | Extra crate |
|-----------|----------------|-------------|
| `peano` (default) | the inductive types as extracted (unary `nat`, binary `positive`/`N`/`Z`) | |
| `gmp` | GMP integers (`rug::Integer`) | `rug` |
| `i64` | `i64`, overflow not checked | |
| `mixed` | GMP integers, with `add`/`mul`/`sub`/`div`/`modulo`/`pow`/`eqb`/`leb`/`ltb` on `nat` computed in `i64` | `rug` |
| `mixed-narrow` | GMP integers, with `div`/`modulo`/`pow` on `nat` computed in `i64` | `rug` |
| `hybrid` | a tagged 63-bit integer while the value fits, GMP integers otherwise, overflow checked | `rug` |

Every representation other than `peano` also maps `bool` to the Rust `bool` and `comparison` to `std::cmp::Ordering`. The generated code always needs the `bumpalo` crate. See [backends.md](backends.md#numeric-representations) for what each representation computes and what is proved about it.

### Eval

`--fuel=N`: the fuel of the evaluator (default 10000). `eval` compiles the program to CertiRocq's $\lambda_{ANF}$ and runs it in the $\lambda_{ANF}$ interpreter, so it takes the CertiRocq options. It prints the value on standard output and needs no other toolchain. It is the cheapest way to check a program end to end.

### Other backends

`ocaml`, `cakeml`, `elm`, `lean`, `fsharp` and `koka` have no options of their own on the command line. Their configuration records ([format.md](format.md#backend-configuration)) are set with `compile` and a configuration file.


## Configuration and attribute files

The backend commands build a default configuration for their backend from the flags above. For control over all fields, write a configuration file and use `compile`. The format is in [format.md](format.md#configuration).

Attribute files ([format.md](format.md#attribute-files)) add inlinings, constant and inductive remappings, constructor reorderings and custom attributes to the configuration, with any command. Uses include:

* reordering constructors, e.g. so that Rocq's `bool` has `false` first like Agda's and Lean's;
* remapping constants to target-language code, e.g. axioms implemented in C or OCaml;
* the inlinings that the Lean frontend writes, which peregrine passes on by itself for a `.lean` input.


## Exit codes

| Code | Meaning |
|------|---------|
| 0 | success |
| 1 | the program is not valid or does not compile, or the output would overwrite a `.lean` input |
| 10–19, 20–29 | listed by `--help` for parsing and compiler errors; not used yet (those errors exit with 1) |
| 30 | the frontend tool is not on the `PATH` |
| 31 | the frontend tool failed |
| 32 | the frontend does not support the request: `--entry` missing for Rocq or Lean, or given for Agda; `--typed` for Lean; `--lean-config` for a frontend other than Lean; frontend options on a $\lambda_\square$ input; `erase` of a $\lambda_\square$ program; a Lean input outside a Lake project |
| 123, 124, 125 | from the command line parser: other errors, command-line errors, internal errors |


## Deprecated commands and options

They keep working, print a warning on standard error, and are not listed by `--help`.

| Deprecated | Use instead |
|------------|-------------|
| `rust-gmp` | `rust --numbers=gmp` |
| `rust-i64` | `rust --numbers=i64` |
| `rust-mixed` | `rust --numbers=mixed` |
| `rust-mixed-narrow` | `rust --numbers=mixed-narrow` |
| `rust-hybrid` | `rust --numbers=hybrid` |
| `--prefix` | nothing; ignored, CertiRocq no longer generates an FFI |
| `--anf-conf` | nothing; ignored, the pipeline does not read it |


## Examples

```bash
# Rocq, in a project whose _RocqProject gives the load path (detected)
peregrine c theories/Main.v --entry main -o build/main.c

# Rocq, with the load path given instead
peregrine c src/Main.v --entry main \
  --frontend-arg=-Q --frontend-arg=theories --frontend-arg=MyLib -o build/main.c

# The same program to Rust, with i64 numbers (typed lambda box from Rocq)
peregrine rust src/Main.v --entry main --numbers=i64 -o main.rs

# Agda, literate, with an include path; keep the lambda box program
peregrine ocaml Main.lagda.md --frontend-arg=-i --frontend-arg=lib --keep-ast main.ast

# Lean, evaluated without any target toolchain, with Nat as an inductive type
peregrine eval Main.lean --entry main --lean-config '{nat := .peano}'

# Force a frontend: a Rocq file with another extension
peregrine erase main.coq --from rocq --entry main -o main.ast

# A lambda box program, with an attribute file and optional passes
peregrine ocaml main.ast --attributes=bool_reorder.attr --cse true --specialize-instances true

# A full pipeline configuration
peregrine compile main.ast config.sexp -o main.c

# Inspect the program after the middle-end
peregrine ast typed main.ast -o main.typed.ast
```
