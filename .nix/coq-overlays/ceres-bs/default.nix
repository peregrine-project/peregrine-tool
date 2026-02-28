{
  lib,
  mkCoqDerivation,
  coq,
  metarocq,
  stdlib,
  version ? null,
}:

mkCoqDerivation {

  pname = "ceres-bs";
  repo = "rocq-ceres-bytestring";
  opam-name = "rocq-ceres-bytestring";
  owner = "peregrine-project";

  inherit version;
  defaultVersion =
    let
      case = case: out: { inherit case out; };
    in
    with lib.versions;
    lib.switch coq.version [
    ] null;

  useDune= true;

  propagatedBuildInputs = [ coq.ocamlPackages.findlib stdlib metarocq ];

  meta = {
    description = "Library for serialization to S-expressions";
    license = lib.licenses.mit;
    maintainers = with lib.maintainers; [ _4ever2 ];
  };
}
