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
  version ? null,
}:

with lib;
mkCoqDerivation {
  pname = "CertiRocq";
  owner = "CertiRocq";
  repo = "certirocq";
  opam-name = "rocq-certirocq";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  buildInputs = [
    pkgs.clang
  ];

  propagatedBuildInputs = [
    wasmcert
    compcert
    ExtLib
    metarocq-erasure-plugin
    metarocq-safechecker-plugin
  ];

  patchPhase = ''
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

    make
    make runtime

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${coq.coq-version}/user-contrib

    DST=$OUTDIR/CertiRocq/Plugin/runtime make -C runtime install
    COQLIBINSTALL=$OUTDIR make -C theories install
    COQLIBINSTALL=$OUTDIR make -C libraries install

    runHook postInstall
  '';

  meta = {
    description = "CertiRocq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
