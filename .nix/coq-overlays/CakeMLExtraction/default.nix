{
  lib,
  mkCoqDerivation,
  coq,
  ceres-bs,
  equations,
  metarocq,
  version ? null,
}:

(mkCoqDerivation {
  pname = "CakeMLExtraction";
  owner = "peregrine-project";
  repo = "cakeml-backend";
  opam-name = "rocq-cakeml-extraction";
  inherit version;
  defaultVersion = null;

  mlPlugin = false;
  useDune = false;

  buildInputs = [ equations metarocq ceres-bs ];
  propagatedBuildInputs = [ coq.ocamlPackages.findlib ];

  meta = with lib; {
    homepage = "https://peregrine-project.github.io/";
    description = "CakeML backend for Peregrine";
    maintainers = with maintainers; [ mattam82 ];
  };
})
