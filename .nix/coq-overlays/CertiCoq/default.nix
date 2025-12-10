{
  lib,
  pkgs,
  pkg-config,
  mkCoqDerivation,
  coq,
  wasmcert,
  compcert,
  metarocq,
  ExtLib,
  version ? null,
}:

with lib;
mkCoqDerivation {
  pname = "CertiCoq";
  owner = "4ever2";
  repo = "certicoq";
  opam-name = "coq-certicoq";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  buildInputs = [
    pkgs.clang
  ];

  propagatedBuildInputs = [
    wasmcert # TODO: enforce 2.2.0
    compcert
    ExtLib
    metarocq # TODO: enforce 1.3.1+8.20
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

    DST=$OUTDIR/CertiCoq/Plugin/runtime make -C runtime install
    COQLIBINSTALL=$OUTDIR make -C theories install
    COQLIBINSTALL=$OUTDIR make -C libraries install

    runHook postInstall
  '';

  meta = {
    description = "CertiCoq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
