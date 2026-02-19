Require Import MetaRocq.Utils.bytestring.

Axiom (coq_msg_info : string -> unit).
Axiom (coq_msg_notice : string -> unit).
Axiom (coq_msg_debug : string -> unit).
Axiom (coq_user_error : string -> unit).
