
{
  lib,
  mkCoqDerivation,
  coq,
  metarocq-erasure-plugin,
  TypedExtraction,
  ceres-bs,
  CertiRocq,
  verified-extraction,
  CakeMLExtraction,
  version ? null
}:

mkCoqDerivation {
  pname = "Peregrine";
  repo = "peregrine-tool";
  owner = "peregrine-project";
  domain = "github.com";
  opam-name = "rocq-peregrine";

  inherit version;
  defaultVersion = with lib.versions; lib.switch coq.coq-version [
  ] null;

  buildInputs = [ coq.ocamlPackages.dune_3 ];
  propagatedBuildInputs = [
    coq.ocamlPackages.cmdliner
    coq.ocamlPackages.findlib
    coq.ocamlPackages.rocq-primitive
    metarocq-erasure-plugin
    TypedExtraction
    ceres-bs
    CertiRocq
    verified-extraction
    CakeMLExtraction
  ];

  mlPlugin = true;
  useDune = false;

  prePatch = ''
    patchShebangs plugin/process_extraction.sh
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${coq.coq-version}/user-contrib

    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR  rocq-peregrine
    COQLIBINSTALL=$OUTDIR make -f RocqMakefile install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugin install

    runHook postInstall
  '';

  meta = {
    description = "The Peregrine Project provides a unified middle-end for code generation from proof assistants.";
    maintainers = with lib.maintainers; [ _4ever2 ];
    license = lib.licenses.mit;
  };
}
