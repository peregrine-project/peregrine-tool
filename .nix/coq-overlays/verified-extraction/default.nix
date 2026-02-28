{
  lib,
  mkCoqDerivation,
  coq,
  dune_3,
  ceres-bs,
  equations,
  metarocq,
  malfunction,
  version ? null,
}:

(mkCoqDerivation {
  pname = "verified-extraction";
  owner = "4ever2";
  repo = "rocq-verified-extraction";
  opam-name = "rocq-verified-extraction";
  inherit version;
  defaultVersion = null;

  mlPlugin = true;
  useDune = false;

  buildInputs = [ dune_3 malfunction equations metarocq ceres-bs ];
  propagatedBuildInputs = [ coq.ocamlPackages.ppx_optcomp coq.ocamlPackages.findlib malfunction ];

  patchPhase = ''
    patchShebangs plugin/plugin/clean_extraction.sh
  '';

  meta = with lib; {
    homepage = "https://metarocq.github.io/";
    description = "Verified Extraction from Rocq to OCaml. Including a bootstrapped extraction plugin";
    maintainers = with maintainers; [ mattam82 ];
  };
})
