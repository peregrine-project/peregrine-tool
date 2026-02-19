Require Import MetaRocq.Utils.bytestring.
From Malfunction.Plugin Require Import Loader.
From Malfunction Require Import FFI.

Verified Extract Constants [ 
  coq_msg_info => "Rocq_verified_extraction_plugin__Rocq_ffi.msg_info",
  coq_msg_notice => "Rocq_verified_extraction_plugin__Rocq_ffi.msg_notice",
  coq_msg_debug => "Rocq_verified_extraction_plugin__Rocq_ffi.msg_debug",
  coq_user_error => "Rocq_verified_extraction_plugin__Rocq_ffi.user_error" ]
Packages [ "rocq_verified_extraction.plugin" ].
