{
  lib,
  coq,
  metaFetch,
  version ? null
}:

let
  ocamlPackages = coq.ocamlPackages;
  defaultVersion =
    let
      case = case: out: { inherit case out; };
    in
    lib.switch coq.coq-version [
      (case "9.0" "9.0.0")
    ] null;
  location = {
    domain = "github.com";
    owner = "peregrine-project";
    repo = "rocq-primitive";
  };
  fetch = metaFetch {
    release."9.0.0".rev = "9.0.0";
    release."9.0.0".sha256 = "sha256-AGVYWIiAe/cmAffV6jDHc166yUg1zDFzUj6b1NvWyvk=";
    inherit location;
  };
  fetched = fetch (if version != null then version else defaultVersion);
in
ocamlPackages.buildDunePackage {
  pname = "rocq-primitive";
  inherit (fetched) version;
  src = "${fetched.src}";
  nativeBuildInputs = [ ];
  buildInputs = [ ];

  meta = with lib; {
    homepage = "https://github.com/peregrine-project/rocq-primitive";
    description = "This library provides OCaml modules for primitive objects in Rocq.";
    license = licenses.lgpl21;
    maintainers = with maintainers; [ _4ever2 ];
  };
}
