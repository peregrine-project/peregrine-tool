From Peregrine Require SerializeCommon.
From Peregrine Require SerializeEAst.
From Peregrine Require SerializeExAst.
From Peregrine Require SerializePAst.
From Peregrine Require SerializeConfig.
From Peregrine Require CeresExtra.



Definition string_of_PAst := SerializePAst.string_of_PAst.

Definition string_of_config := SerializeConfig.string_of_config'.

Definition string_of_backend_config := SerializeConfig.string_of_backend_config'.

Definition string_of_erasure_phases := SerializeConfig.string_of_erasure_phases'.

Definition string_of_attributes_config := SerializeConfig.string_of_attributes_config.
