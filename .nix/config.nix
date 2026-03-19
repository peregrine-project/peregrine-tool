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

      metarocq-utils.override.version = "1.5.1-9.1";
      metarocq-common.override.version = "1.5.1-9.1";
      metarocq-template-rocq.override.version = "1.5.1-9.1";
      metarocq-pcuic.override.version = "1.5.1-9.1";
      metarocq-safechecker.override.version = "1.5.1-9.1";
      metarocq-safechecker-plugin.override.version = "1.5.1-9.1";
      metarocq-template-pcuic.override.version = "1.5.1-9.1";
      metarocq-erasure.override.version = "1.5.1-9.1";
      metarocq-erasure-plugin.override.version = "1.5.1-9.1";

      TypedExtraction.override.version = "0.2.1";
      CertiRocq.override.version = "0.9.1+9.1";
      verified-extraction.override.version = "1.0.0-9.1";
      ceres-bs.override.version = "1.0.0";
      CakeMLExtraction.override.version = "0.1.0";
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
