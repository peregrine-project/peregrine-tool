
{ lib, mkCoqDerivation, which, coq
  , metarocq, TypedExtraction
  , ceres, CertiCoq, verified-extraction
  , coq-primitive
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "Peregrine";
  repo = "peregrine-tool";
  owner = "peregrine-project";
  domain = "github.com";
  opam-name = "rocq-peregrine";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;

  propagatedBuildInputs = [
    coq.ocamlPackages.cmdliner
    coq.ocamlPackages.findlib
    coq.ocamlPackages.dune_3
    metarocq
    TypedExtraction
    ceres
    CertiCoq
    verified-extraction
    coq-primitive
  ];

  mlPlugin = true;
  useDune = true;

  preBuild = ''
    make theory
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR  rocq-peregrine
    runHook postInstall
  '';

  meta = {
    description = "A framework for extracting lambda box programs";
    maintainers = with maintainers; [ _4ever2 ];
    license = licenses.mit;
  };
}
