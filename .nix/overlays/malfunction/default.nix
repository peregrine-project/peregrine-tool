{
  lib,
  fetchzip,
  ocaml-ng,
}@args:

ocaml-ng.ocamlPackages_4_14.buildDunePackage {
  pname = "malfunction";
  defaultVersion = "0.7.1";
  version = "0.7.1";

  src = fetchzip {
    url = "https://github.com/stedolan/malfunction/archive/refs/tags/v0.7.1.tar.gz";
    hash = "sha256-Cpe5rSBvsr3pqbucGZelutPoI+bcQPFCbdcKsE/HieY=";
  };

  duneVersion = "3";

  buildInputs = with ocaml-ng.ocamlPackages_4_14; [
    ocaml
    findlib
    zarith
    ppx_optcomp
    cppo
  ];
  nativeBuildInputs = with ocaml-ng.ocamlPackages_4_14; [
    ocaml
    cppo
    findlib
  ];

  meta = with lib; {
    homepage = "http://github.com/stedolan/malfunction";
    description = "Malfunction is a high-performance, low-level untyped program representation, designed as a target for compilers of functional programming languages.";
    license = licenses.lgpl21;
    maintainers = [ ];
    mainProgram = "malfunction";
  };
}
