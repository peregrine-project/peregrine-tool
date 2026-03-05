{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "Peregrine";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = { coqPackages = {
      coq.override.version = "9.1";
      metarocq.override.version = "1.4.1-9.1";
      TypedExtraction.override.version = "0.2.0";
      CertiCoq.override.version = "coq-9.1";
      verified-extraction.override.version = "rocq-9.1-bs";
      ceres-bs.override.version = "master";
      CakeMLExtraction.override.version = "ceres-bs";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
  };

  bundles."9.1".push-branches = ["master"];

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.peregrine.authToken = "CACHIX_AUTH_TOKEN";
}
