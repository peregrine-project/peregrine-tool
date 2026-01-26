{
  lib,
  fetchzip,
  ocaml-ng
}@args:

ocaml-ng.ocamlPackages_4_14.buildDunePackage {
  pname = "rocq-primitive";
  defaultVersion = "9.0";
  version = "9.0";

  src = fetchzip {
    url = "https://github.com/palmskog/rocq-primitive/archive/refs/heads/v9.0.tar.gz";
    hash = "sha256-AGVYWIiAe/cmAffV6jDHc166yUg1zDFzUj6b1NvWyvk=";
  };

  duneVersion = "3";


  buildInputs = with ocaml-ng.ocamlPackages_4_14; [ ocaml findlib ];
  nativeBuildInputs = with ocaml-ng.ocamlPackages_4_14; [
    ocaml
    findlib
  ];

  meta = with lib; {
    homepage = "https://github.com/palmskog/rocq-primitive";
    description = "This library provides OCaml modules for primitive objects in Rocq.";
    license = licenses.lgpl21;
    maintainers = with maintainers; [ _4ever2 ];
  };
}
