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

      # The rust-rc-memory branch of peregrine-project/rocq-typed-extraction, see rocq-peregrine.opam
      TypedExtraction.override.version = "6f94d87c14768feaee3699ad2164eaf12f64431e";
      # The peregrine branch of peregrine-project/certirocq, see rocq-peregrine.opam
      CertiRocq.override.version = "a8dc26feadde902e109ae3a1bbdfacadfc4bb9f6";
      # CertiRocq needs coq-wasm >= 2.2.1
      wasmcert.override.version = "2.2.1";
      verified-extraction.override.version = "0305df76ac89a83488f12175e2c5d45e1a55d16c";
      ceres-bs.override.version = "1.0.0";
      CakeMLExtraction.override.version = "8df83a16525ca08bb9b5b375b3331b3f480d346b";
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
