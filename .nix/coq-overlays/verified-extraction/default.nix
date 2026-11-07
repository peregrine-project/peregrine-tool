{
  lib,
  mkCoqDerivation,
  coq,
  dune,
  ceres-bs,
  equations,
  metarocq-erasure-plugin,
  version ? null,
}:

mkCoqDerivation {
  pname = "verified-extraction";
  # The MetaRocq 9.1 snapshot port, from the peregrine branch of
  # peregrine-project/rocq-verified-extraction, see rocq-peregrine.opam.
  owner = "peregrine-project";
  repo = "rocq-verified-extraction";
  opam-name = "rocq-verified-extraction";

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
    lib.switch
      [
        coq.coq-version
        metarocq-erasure-plugin.version
      ]
      [
        (case "9.1" "1.5.1-9.1" "1.0.0-9.1")
      ]
      null;
  release = {
    "1.0.0-9.1".hash = "sha256-0eKpchQtnPI12rcsb9+qN1pdNX9KY8VryZP0oqHuYeU=";
    # the peregrine branch, see rocq-peregrine.opam
    "0ed8aa88560a518e0822b583f45e1ebb45b10f7f" = {
      rev = "0ed8aa88560a518e0822b583f45e1ebb45b10f7f";
      hash = "sha256-cjUNf3Zq6x/nA+WY+nqDwhulhuxOBg0o5wizS+L80ws=";
    };
  };
  releaseRev = v: "v${v}";

  mlPlugin = true;

  buildInputs = [ dune ];
  propagatedBuildInputs = [
    coq.ocamlPackages.findlib
    coq.ocamlPackages.malfunction
    equations
    metarocq-erasure-plugin
    ceres-bs
  ];

  prePatch = ''
    patchShebangs plugin/plugin/clean_extraction.sh
  '';

  meta = with lib; {
    homepage = "https://metarocq.github.io/";
    description = "Verified Extraction from Rocq to OCaml. Including a bootstrapped extraction plugin";
    maintainers = with maintainers; [
      mattam82
      _4ever2
    ];
  };
}
