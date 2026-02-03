From Peregrine Require SerializeCommon.
From Peregrine Require SerializeEAst.
From Peregrine Require SerializeExAst.
From Peregrine Require SerializePAst.
From Peregrine Require SerializeConfig.
From Peregrine Require CeresExtra.



Definition program_of_string := SerializeEAst.program_of_string.

Definition global_env_of_string := SerializeExAst.global_env_of_string.

Definition kername_of_string := SerializeCommon.kername_of_string.

Definition string_of_error := CeresExtra.string_of_error.

Definition PAst_of_string := SerializePAst.PAst_of_string.

Definition config_of_string := SerializeConfig.config'_of_string.
