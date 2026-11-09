# Dependencies

This page lists what peregrine-tool depends on, where each dependency lives and which version or commit is pinned. The tables give the state of master on 2026-11-07; the files under [Where the pins are recorded](#where-the-pins-are-recorded) are authoritative, so check them when the two disagree.

## Policy for forks in peregrine-project

Some upstream projects need minor changes. For these, `peregrine-project` keeps a fork:

- The fork's **mirror branch** is the upstream default branch, kept equal to upstream, with no commits of our own. It is `main` for certirocq and `rocq-9.1` for rocq-verified-extraction.
- The **`peregrine` branch** is the mirror branch plus our edits on top. The edits should stay small, and each one is meant to go upstream as a pull request.
- peregrine-tool **pins a commit of the `peregrine` branch**, never a branch name, so a push to the fork never changes the build.
- **To pick up upstream changes:**
  1. fast-forward the mirror branch to upstream;
  2. merge the mirror branch into `peregrine`;
  3. move the pin (see [Updating a pin](#updating-a-pin)).

  When upstream merges one of our edits, it drops out of the `peregrine` diff on the next merge.

rocq-ceres-bytestring is an older fork that follows a different model. It is a renamed package with its own releases. See its row below.

## Rocq libraries (peregrine-tool and the Rocq frontend)

The Rocq frontend ([plugin/](/plugin/)) is built with peregrine-tool and has the same dependencies.

| Package | Pin | Repository | Branch | Used by |
|---|---|---|---|---|
| `rocq-core`, `rocq-runtime` | 9.1.1 | rocq-prover/rocq | release | everything |
| `rocq-stdlib` | 9.0.0 | rocq-prover/stdlib | release | everything |
| MetaRocq: `utils`, `common`, `template`, `pcuic`, `template-pcuic`, `safechecker`, `safechecker-plugin`, `erasure`, `erasure-plugin` | `51b14e4b` (version renamed `1.5.1+9.1+dev`) | [MetaRocq/metarocq](https://github.com/MetaRocq/metarocq) | upstream, unreleased snapshot of the 9.1 branch, which CertiRocq `main` expects; release 1.5.1 lacks `EImplementLazyForce` | λ□ syntax and semantics, erasure (Rocq frontend), middle-end |
| `rocq-certirocq` | `4cf32ff2` (version `dev`) | [peregrine-project/certirocq](https://github.com/peregrine-project/certirocq) (fork of CertiRocq/certirocq) | `peregrine`: CertiRocq `main` at `943b52ae` plus the LLVM backend (upstream PR CertiRocq/certirocq#155), Peregrine fixes, the shadow-stack change (no frame for a call with no live root) and the tail-call rewrite of a `match` in tail position (`Eletapp x f ys (Ehalt x)` becomes `Eapp f ys`, peregrine-project/certirocq#4) | `c`, `wasm`, `llvm`, `eval` |
| `rocq-vellvm` | `b63a28a0` (version `dev`) | [vellvm/vellvm](https://github.com/vellvm/vellvm) | upstream, unreleased | `llvm` (through CertiRocq) |
| `rocq-verified-extraction` | `0ed8aa88` (version `1.0.0+9.1+dev`) | [peregrine-project/rocq-verified-extraction](https://github.com/peregrine-project/rocq-verified-extraction) (fork of MetaRocq/rocq-verified-extraction) | `peregrine`: a merge of `rocq-9.1` at `64ced8c0`, with the same tree; upstream now has our `switch_no_params` edit (MetaRocq/rocq-verified-extraction#44) | `ocaml` |
| `rocq-cakeml-extraction` | `8df83a16` (version `0.1.1+dev`) | [peregrine-project/cakeml-backend](https://github.com/peregrine-project/cakeml-backend) | `fix-datatype-decls-snapshot`, the head of open PR #16, which is stacked on open PR #13 (`metarocq-9.1-snapshot` into `rocq-9.1`); `main` is not used | `cakeml` |
| `rocq-typed-extraction-common`, `rocq-rust-extraction`, `rocq-elm-extraction` | `74dcbc96` (version `0.2.1`) | [peregrine-project/rocq-typed-extraction](https://github.com/peregrine-project/rocq-typed-extraction) | `metarocq-51b14e4b`: release tag `v0.2.1` ported to MetaRocq `51b14e4b` (a qualified `Import String` in `PrettyPrinterMonad.v`, and the plugin's lists of extracted modules) | `rust`, `elm`, `Peregrine Extract Typed` |
| `rocq-ceres-bytestring` | 1.0.0 | [peregrine-project/rocq-ceres-bytestring](https://github.com/peregrine-project/rocq-ceres-bytestring) (fork of Lysxia/coq-ceres, renamed) | release, from `rocq-released` | S-expression (de)serialization |
| `rocq-primitive` | 9.0.0 | [peregrine-project/rocq-primitive](https://github.com/peregrine-project/rocq-primitive) | release | primitive types |
| `rocq-mathcomp-ssreflect` | 2.5.0 | math-comp/math-comp | release; CertiRocq needs it below 2.6 | CertiRocq |

These come in through CertiRocq and verified extraction, at the versions those packages allow:

| Package | Version | Requirement |
|---|---|---|
| `coq-compcert` | 3.17 | required exactly by CertiRocq |
| `rocq-equations` | 1.3.1+9.1 | required exactly by CertiRocq |
| `coq-wasm` (WasmCert-Coq) | 2.2.1 | CertiRocq requires at least this version; it needs `rocq-parseque` 0.3.1 |
| `coq-ext-lib` | any | CertiRocq requires at least 0.12 |
| `malfunction` | 0.7.1 | verified extraction requires at least this version; it is also needed to compile `.mlf` output |
| ITree, Paco, Flocq | — | not pinned by Peregrine; whatever Vellvm and CompCert pull in |

OCaml is 4.14.2 (CI: `ocaml-variants.4.14.2+options` with flambda), and `cmdliner` is 2.1.0.

## Other parts of this repository

| Part | Dependencies | Recorded in |
|---|---|---|
| [hs-lib/](/hs-lib/) (Haskell serializers) | `base` ≥ 4.20 and < 4.22, `ghc-internal`, `deepseq`, `bytestring`, `text` | `hs-lib/lambdabox.cabal` |
| [lean/](/lean/) (runtime of the Lean backend) | Lean `v4.34.1`, no Lake packages | `lean-toolchain`, `lakefile.toml` |
| [test/lean](/test/lean/) (Lean fixtures of the test suite) | Lean `v4.22.0`, lean-to-lambdabox at `42f8f510` | `test/lean/lean-toolchain`, `test/lean/lake-manifest.json` |

The two Lean toolchains differ on purpose: the backend runtime and the Lean frontend are pinned independently.

## Frontends outside this repository

| Frontend | Repository | Default branch | Its own dependencies | Pinned by peregrine-tool's CI |
|---|---|---|---|---|
| Agda | [agda/agda2lambox](https://github.com/agda/agda2lambox) | `master` | GHC 9.10.1, cabal 3.12.1, Agda ≥ 2.8 and < 2.9 (built with `+debug`), `sexpresso` 1.2.5; its own λ□ syntax in `src/LambdaBox/` | `6d680804` (`.github/workflows/build.yml`) |
| Lean | [peregrine-project/lean-to-lambdabox](https://github.com/peregrine-project/lean-to-lambdabox) | `main` | Lean `v4.22.0`, no Lake packages | `42f8f510` (`test/lean/lake-manifest.json`) |

## Target toolchains in CI

These versions come from `.github/workflows/build.yml`. They are what the test suite runs against, not hard requirements of `peregrine` itself.

| Target | Toolchain |
|---|---|
| `rust` | Rust 1.85.0; crates `bumpalo`, and `rug` for the GMP numbers |
| `elm` | Elm 0.19.1, elm-test 0.19.1-revision9, Node 22 |
| `wasm` | Node 22 (its WebAssembly API runs the module) |
| `llvm` | clang-15 |
| `koka` | Koka v3.2.9 |
| `ocaml` | `malfunction` 0.7.1 and OCaml 4.14.2 |
| `lean` | the toolchain in `lean-toolchain` (installed with elan) |

## Projects that pin peregrine-tool

| Project | Pin | Where |
|---|---|---|
| agda2lambox CI | `8077cfd` (2026-10-22) | agda2lambox's `.github/workflows/ci.yml` |
| benchmarks | `dae0fb4e` (tag `master-2026-11-06`) | `toolchain.mk` (`PEREGRINE_REV`) |

## Where the pins are recorded

Three files must agree on every Rocq-side pin:

- [`rocq-peregrine.opam`](/rocq-peregrine.opam): version constraints, and `pin-depends` for the unreleased packages (CertiRocq, Vellvm, MetaRocq, verified extraction, CakeML, TypedExtraction);
- [`.github/rocq-peregrine.opam.locked`](/.github/rocq-peregrine.opam.locked): the exact versions CI installs;
- [`.nix/config.nix`](/.nix/config.nix): the same versions and commits for the Nix bundle `9.1`.

## Updating a pin

1. For a fork, follow the [policy](#policy-for-forks-in-peregrine-project): sync the mirror branch, merge it into `peregrine` and pin the resulting commit.
2. Change the commit or version in all three files above, and in the comment next to it in `rocq-peregrine.opam`.
3. Rebuild from scratch (`make theory mllib`) and run the full test suite (`test/`).
4. If the λ□ format or a frontend-facing interface changed, update the consumers too: the lean-to-lambdabox pin in `test/lean`, agda2lambox's pin of peregrine-tool, and benchmarks' `toolchain.mk`.
5. Never raise a pin just to get something to build; use the pinned versions.

## Known drift (2026-11-07)

- **certirocq:** the fork's `main` (`f1e46a48`) is 26 commits behind CertiRocq `main` (`943b52ae`). The pin is the head of `peregrine`, which already merges upstream `943b52ae`.
- **MetaRocq:** the pin is the head of the 9.1 branch.
- **rocq-verified-extraction:** the fork's `rocq-9.1` equals upstream (`64ced8c0`). The pin is the head of `peregrine`.
- **cakeml-backend:** the pin is the head of open PR #16, which is stacked on open PR #13. Merging #13 and then #16 would put the pin on a regular branch.
- **rocq-typed-extraction:** the pin is `v0.2.1` plus the port to MetaRocq `51b14e4b`, on the branch `metarocq-51b14e4b`; `master` is 35 commits past `v0.2.1` and needs the same port (branch `metarocq-51b14e4b-master`). The Rust printer fixes for #127 (rocq-typed-extraction #19, #20 and #24) are on `master` only.
- **lean-to-lambdabox:** the test pin `42f8f510` (2026-02-17) is older than `main` (`58701f8b`, 2026-06-22). The manifest's `inputRev` names a branch, `ast-format`, that no longer exists; the commit itself is on `main`.
- **agda2lambox:** its CI pins peregrine-tool `8077cfd`, from before the CertiRocq fork pin.
