From Peregrine Require SerializeCommon.
From Peregrine Require SerializeEAst.
From Peregrine Require SerializeExAst.
From Peregrine Require SerializePAst.
From Peregrine Require SerializeConfig.
From Peregrine Require CeresExtra.



Definition string_of_error := CeresExtra.string_of_error.

Definition PAst_of_string := SerializePAst.PAst_of_string.

Definition config_of_string := SerializeConfig.config'_of_string.

Definition backend_config_of_string := SerializeConfig.backend_config'_of_string.

Definition erasure_phases_of_string := SerializeConfig.erasure_phases'_of_string.

Definition attributes_config_of_string := SerializeConfig.attributes_config_of_string.
