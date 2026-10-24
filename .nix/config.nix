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
      # TODO(#155): the commit of CertiRocq/certirocq main that merges #155
      CertiRocq.override.version = "6b4ab87014ccdddf69ea4a9278c4974ba671ca2d";
      # CertiRocq needs coq-wasm >= 2.2.1
      wasmcert.override.version = "2.2.1";
      verified-extraction.override.version = "16de6e9f67b1085ef519095433f96f8b1067febe";
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
