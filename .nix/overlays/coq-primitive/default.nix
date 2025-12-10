{
  lib,
  fetchzip,
  ocaml-ng
}@args:

ocaml-ng.ocamlPackages_4_14.buildDunePackage {
  pname = "coq-primitive";
  defaultVersion = "8.20";
  version = "8.20";

  src = fetchzip {
    url = "https://github.com/4ever2/coq-primitive/archive/refs/heads/v8.20.tar.gz";
    hash = "sha256-kwx/v7rTopHgedsdFnSnMm9QISiyX7ffgQzsCYlDLJA=";
  };

  duneVersion = "3";


  buildInputs = with ocaml-ng.ocamlPackages_4_14; [ ocaml findlib ];
  nativeBuildInputs = with ocaml-ng.ocamlPackages_4_14; [
    ocaml
    findlib
  ];

  meta = with lib; {
    homepage = "https://github.com/palmskog/coq-primitive";
    description = "This library provides OCaml modules for primitive objects in Coq.";
    license = licenses.lgpl21;
    maintainers = with maintainers; [ _4ever2 ];
  };
}
