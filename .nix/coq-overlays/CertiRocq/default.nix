{
  lib,
  pkgs,
  pkg-config,
  mkCoqDerivation,
  coq,
  wasmcert,
  compcert,
  metarocq-erasure-plugin,
  metarocq-safechecker-plugin,
  ExtLib,
  vellvm,
  version ? null,
}:

mkCoqDerivation {
  pname = "CertiRocq";
  # CertiRocq with the LLVM backend (CertiRocq/certirocq#155), see
  # rocq-peregrine.opam. TODO(#155): owner = "CertiRocq" and the merge commit.
  owner = "barabbs";
  repo = "certirocq";
  opam-name = "rocq-certirocq";
  mlPlugin = true;

  inherit version;
  defaultVersion =
    let
      case = coq: mr: out: {
        cases = [
          coq
          mr
        ];
        inherit out;
      };
    in
    lib.switch
      [
        coq.coq-version
        metarocq-erasure-plugin.version
      ]
      [
        (case "9.1" "c8cd46054518193103c3bb33aa6e15c7f489e72c" "6b4ab87014ccdddf69ea4a9278c4974ba671ca2d")
      ]
      null;
  release = {
    "6b4ab87014ccdddf69ea4a9278c4974ba671ca2d" = {
      rev = "6b4ab87014ccdddf69ea4a9278c4974ba671ca2d";
      hash = "sha256-XEFhXNE7G1QVmN6CWb8N0jF7jIIyxo9UFvHkkXxNKSU=";
    };
  };

  buildInputs = [
    pkgs.clang
    pkgs.python3
  ];

  propagatedBuildInputs = [
    wasmcert
    compcert
    ExtLib
    vellvm
    metarocq-erasure-plugin
    metarocq-safechecker-plugin
  ];

  prePatch = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
    substituteInPlace ./runtime/Makefile \
      --replace 'gcc' 'cc' \
      --replace 'DST =' 'DST ?='
  '';

  configurePhase = ''
    ./configure.sh local
  '';

  buildPhase = ''
    runHook preBuild

    make all
    make plugins

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${coq.coq-version}/user-contrib

    DST=$OUTDIR/CertiRocq/Plugin/runtime make -C runtime install
    COQLIBINSTALL=$OUTDIR make -C theories install
    COQLIBINSTALL=$OUTDIR make -C libraries install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugins/plugin install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugins/cplugin install

    runHook postInstall
  '';

  meta = {
    description = "CertiRocq";
    maintainers = with lib.maintainers; [ womeier _4ever2 ];
    license = lib.licenses.mit;
  };
}
