{
  lib,
  fetchzip,
  ocaml-ng
}@args:

ocaml-ng.ocamlPackages_4_14.buildDunePackage {
  pname = "malfunction";
  defaultVersion = "0.7";
  # lib.switch ocamlPackages.ocaml.version [ { case = lib.range "4.0" "4.14.2"; out = "0.4.1"; } ] null;
  version = "0.7";

  src = fetchzip {
    url = "https://github.com/stedolan/malfunction/archive/refs/tags/v0.7.tar.gz";
    hash = "sha256-qXaAkpKKQL2o+E3vvPeNeBmu5qFfBKw6BewW/g7dqSw=";
  };

  duneVersion = "3";

  #preBuild = ''
   # substituteInPlace Makefile --replace /bin/rm rm --replace /usr/local/ $out/
  #'';


  buildInputs = with ocaml-ng.ocamlPackages_4_14; [ ocaml findlib zarith ppx_optcomp cppo ];
  nativeBuildInputs = with ocaml-ng.ocamlPackages_4_14; [
    ocaml
    cppo
    findlib
  ];

  meta = with lib; {
    homepage = "http://github.com/stedolan/malfunction";
    description = "Malfunction is a high-performance, low-level untyped program representation, designed as a target for compilers of functional programming languages.";
    license = licenses.lgpl21;
    maintainers = [ mattam82 ];
    mainProgram = "malfunction";
  };
}
