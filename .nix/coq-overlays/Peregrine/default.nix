
{
  lib,
  mkCoqDerivation,
  which,
  coq,
  metarocq-erasure-plugin,
  TypedExtraction,
  ceres-bs,
  CertiRocq,
  verified-extraction,
  rocq-primitive,
  CakeMLExtraction,
  dune,
  version ? null
}:

with lib; mkCoqDerivation {
  pname = "Peregrine";
  repo = "peregrine-tool";
  owner = "peregrine-project";
  domain = "github.com";
  opam-name = "rocq-peregrine";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;

  buildInputs = [ dune ];
  propagatedBuildInputs = [
    coq.ocamlPackages.cmdliner
    coq.ocamlPackages.findlib
    coq.ocamlPackages.dune_3
    metarocq-erasure-plugin
    TypedExtraction
    ceres-bs
    CertiRocq
    verified-extraction
    CakeMLExtraction
    rocq-primitive
  ];

  mlPlugin = true;
  useDune = false;

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
    maintainers = with maintainers; [ _4ever2 ];
    license = licenses.mit;
  };
}
