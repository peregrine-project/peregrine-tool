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
    "eaf5375613cc5c34507ca2601c7761df2797a47d" = {
      rev = "eaf5375613cc5c34507ca2601c7761df2797a47d";
      hash = "sha256-MFo43e4k/hiod3L8nggUGsu9dqDblr9VIy4IN+TQ/3I=";
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
