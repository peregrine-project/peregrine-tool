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
        (case "9.1" "c8cd46054518193103c3bb33aa6e15c7f489e72c" "a8dc26feadde902e109ae3a1bbdfacadfc4bb9f6")
      ]
      null;
  release = {
    "a8dc26feadde902e109ae3a1bbdfacadfc4bb9f6" = {
      rev = "a8dc26feadde902e109ae3a1bbdfacadfc4bb9f6";
      hash = "sha256-1PtRnC8fL+PfLjXjGC0y+kMvIjtczSscpTnVElK93lo=";
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
