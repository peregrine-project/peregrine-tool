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
  # The LLVM backend is only in this fork: CertiRocq 0.9.1+9.1 plus
  # CodegenLLVM, see rocq-peregrine.opam
  owner = "spitters";
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
        (case "9.1" "1.5.1-9.1" "0.9.1+9.1+llvm")
      ]
      null;
  release = {
    "0.9.1+9.1+llvm" = {
      rev = "13e3f16fcfa79bd0b8246640bf6b71d29ff1cba9";
      hash = "sha256-tOprWbR+w2YXfVKHnvLJQqo785PsSYOo/G/VhqVsmsA=";
    };
  };

  buildInputs = [
    pkgs.clang
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
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugin install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C cplugin install

    runHook postInstall
  '';

  meta = {
    description = "CertiRocq";
    maintainers = with lib.maintainers; [ womeier _4ever2 ];
    license = lib.licenses.mit;
  };
}
