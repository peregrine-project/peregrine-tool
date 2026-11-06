# A shell for running the test suite (test/) under Nix:
#
#   NIXPKGS_ALLOW_UNFREE=1 nix-shell .nix/test-shell.nix
#
# CompCert, which CertiRocq needs, has an unfree licence, hence the variable
# (the Nix CI jobs set it too).
#
# It has the build inputs of the Peregrine package of default.nix (bundle 9.1:
# Rocq, MetaRocq, CertiRocq, verified extraction and the other pins of
# config.nix, from the peregrine cachix cache) and the target toolchains that
# test/ calls.  The toolchains come from the nixpkgs that coq-nix-toolbox pins,
# so their versions can differ from those of build.yml (Rust 1.85.0,
# Elm 0.19.1, elm-test 0.19.1-revision9, Node 22, clang-15, Koka v3.2.9).
# Lean comes through elan, which installs the toolchains named in
# lean-toolchain and test/lean/lean-toolchain on first use.  The Agda and Lean
# frontends (agda2lambox, lean-to-lambdabox) are not included.
let
  peregrine = import ../default.nix { };
  pkgs = import peregrine.initial.nixpkgs { };
in
pkgs.mkShell {
  inputsFrom = [ peregrine ];
  packages = with pkgs; [
    rustc
    cargo
    elmPackages.elm
    elmPackages.elm-test
    nodejs_22
    clang_15
    koka
    elan
    gmp
    pkg-config
  ];
}
