
{ lib, mkCoqDerivation, which, coq
  , metarocq, ElmExtraction, RustExtraction
  , ceres, CertiCoq, verified-extraction
  , coq-primitive
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "lambda-box-extraction";
  repo = "lambda-box-extraction";
  owner = "AU-COBRA";
  domain = "github.com";
  opam-name = "rocq-lambda-box-extraction";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;

  propagatedBuildInputs = [
    coq.ocamlPackages.cmdliner
    coq.ocamlPackages.findlib
    coq.ocamlPackages.dune_3
    metarocq
    ElmExtraction
    RustExtraction
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
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR  rocq-lambda-box-extraction
    runHook postInstall
  '';

  meta = {
    description = "A framework for extracting lambda box programs";
    maintainers = with maintainers; [ _4ever2 ];
    license = licenses.mit;
  };
}
