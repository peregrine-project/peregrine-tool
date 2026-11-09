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

      metarocq-utils.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-common.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-template-rocq.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-pcuic.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-safechecker.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-safechecker-plugin.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-template-pcuic.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-erasure.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-erasure-plugin.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";

      # v0.2.1 ported to the MetaRocq snapshot, see rocq-peregrine.opam
      TypedExtraction.override.version = "0a487b3fa8103c1eabae533cc310634da576e2b4";
      # The peregrine branch of peregrine-project/certirocq, see rocq-peregrine.opam
      CertiRocq.override.version = "067211eb142f12e8d73f143ab4e1ce5db561e219";
      # CertiRocq needs coq-wasm >= 2.2.1
      wasmcert.override.version = "2.2.1";
      verified-extraction.override.version = "0ed8aa88560a518e0822b583f45e1ebb45b10f7f";
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
