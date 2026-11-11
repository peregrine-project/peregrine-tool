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
  # CertiRocq with the LLVM backend, from the peregrine branch of
  # peregrine-project/certirocq, see rocq-peregrine.opam.
  owner = "peregrine-project";
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
        (case "9.1" "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56" "1396dbfa9738254c1837b61f8a0242277e2dd506")
      ]
      null;
  release = {
    "1396dbfa9738254c1837b61f8a0242277e2dd506" = {
      rev = "1396dbfa9738254c1837b61f8a0242277e2dd506";
      hash = "sha256-rNmNPryo4cUWGANymJMjyplRubDSTeXOUseBWPYte6U=";
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
