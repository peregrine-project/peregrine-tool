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
    # ported to the MetaRocq 9.1 snapshot, with datatype declarations (cakeml-backend#16), see rocq-peregrine.opam
    "8df83a16525ca08bb9b5b375b3331b3f480d346b" = {
      rev = "8df83a16525ca08bb9b5b375b3331b3f480d346b";
      hash = "sha256-eaKUaN856DouqtXeCHwbLAkQJODEX9hFjonvSznTnb0=";
    };
    # TODO: PLACEHOLDER.  The compiler correctness proof ported onto 8df83a16
    # (cakeml-backend e2e-snapshot), a local commit that is not pushed yet:
    # replace rev by the pushed commit and hash by its real source hash.
    "dae906dee07e3e0c7bc6de3229a3d7ea66a645dd" = {
      rev = "dae906dee07e3e0c7bc6de3229a3d7ea66a645dd";
      hash = lib.fakeHash;
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
