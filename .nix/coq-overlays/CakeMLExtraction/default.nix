{
  lib,
  mkCoqDerivation,
  coq,
  ceres-bs,
  equations,
  metarocq-erasure-plugin,
  version ? null,
}:

mkCoqDerivation {
  pname = "CakeMLExtraction";
  owner = "peregrine-project";
  repo = "cakeml-backend";
  opam-name = "rocq-cakeml-extraction";

  inherit version;
  defaultVersion =
    let
      case = coq: mr: out: {
        cases = [
          coq
          mr
        ];
        inherit out;
      };
    in
    with lib.versions;
    lib.switch
      [
        coq.coq-version
        metarocq-erasure-plugin.version
      ]
      [
        (case (range "9.0" "9.1") (range "1.4" "1.5.1") "0.1.0")
      ]
      null;
  release = {
    "0.1.0".hash = "sha256-diDUTj0l4vliov9+Lg8lNRdkLE7JAfJn8OU7J/HgmDE=";
    # 0.1.0 ported to the MetaRocq 9.1 snapshot, see rocq-peregrine.opam
    "3c47a631d9a6a591e33bcfb72e277844982dd4b0" = {
      rev = "3c47a631d9a6a591e33bcfb72e277844982dd4b0";
      hash = "sha256-XTfyd5v+f50ZqK/MQ4O9PywnCIDFCoM5w87aIBEpJpM=";
    };
  };
  releaseRev = v: "v${v}";

  propagatedBuildInputs = [
    coq.ocamlPackages.findlib
    equations
    metarocq-erasure-plugin
    ceres-bs
  ];

  meta = with lib; {
    homepage = "https://peregrine-project.github.io/";
    description = "CakeML backend for Peregrine";
    maintainers = with maintainers; [ _4ever2 ];
  };
}
