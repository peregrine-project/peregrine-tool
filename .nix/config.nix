{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "Peregrine";

  no-rocq-yet = true;

  default-bundle = "9.0";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    rocqPacakges.rocq-core.override.version = "9.0";
    coqPackages.metarocq.override.version = "1.4-9.0";
    coqPackages.TypedExtraction.override.version = "rocq-9.0";
    coqPackages.CertiCoq.override.version = "coq-9.0";
    coqPackages.verified-extraction.override.version = "ceres-bs";
    coqPackages.ceres-bs.override.version = "master";
    coqPackages.CakeMLExtraction.override.version = "ceres-bs";
  };

  bundles."9.0".push-branches = ["master"];

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.peregrine.authToken = "CACHIX_AUTH_TOKEN";
}
