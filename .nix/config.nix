{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "Peregrine";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";

      metarocq-utils.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-common.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-template-rocq.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-pcuic.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-safechecker.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-safechecker-plugin.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-template-pcuic.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-erasure.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";
      metarocq-erasure-plugin.override.version = "c8cd46054518193103c3bb33aa6e15c7f489e72c";

      TypedExtraction.override.version = "0.2.1";
      # The peregrine branch of peregrine-project/certirocq, see rocq-peregrine.opam
      CertiRocq.override.version = "a8dc26feadde902e109ae3a1bbdfacadfc4bb9f6";
      # CertiRocq needs coq-wasm >= 2.2.1
      wasmcert.override.version = "2.2.1";
      verified-extraction.override.version = "0305df76ac89a83488f12175e2c5d45e1a55d16c";
      ceres-bs.override.version = "1.0.0";
      CakeMLExtraction.override.version = "3c47a631d9a6a591e33bcfb72e277844982dd4b0";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
    push-branches = [ "master" "rocq-9.1" ];
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};
  cachix.peregrine.authToken = "CACHIX_AUTH_TOKEN";
}
