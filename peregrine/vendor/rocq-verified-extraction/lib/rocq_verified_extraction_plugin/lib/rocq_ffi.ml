open Metarocq_template_plugin

let msg_info msg = 
  Feedback.msg_info Pp.(str (Caml_bytestring.caml_string_of_bytestring msg))

let msg_notice msg = 
  Feedback.msg_notice Pp.(str (Caml_bytestring.caml_string_of_bytestring msg))

let msg_debug msg = 
  Feedback.msg_debug Pp.(str (Caml_bytestring.caml_string_of_bytestring msg))

let user_error msg = 
  CErrors.user_err Pp.(str (Caml_bytestring.caml_string_of_bytestring msg))
