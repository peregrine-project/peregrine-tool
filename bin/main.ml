open Cmdliner
open Compile
open Common

let version = "0.0.1"

let copts_t =
  let docs = Manpage.s_common_options in
  let verbose_arg =
    let doc = "Suppress informational output." in
    let quiet = Quiet, Arg.info ["q"; "quiet"] ~docs ~doc in
    let doc = "Give verbose output: print the command that runs the frontend." in
    let verbose = Verbose, Arg.info ["v"; "verbose"] ~docs ~doc in
    Arg.(last & vflag_all [Normal] [quiet; verbose])
  in
  let debug_arg =
    let doc = "Keep the temporary directory of the frontend and print its path." in
    Arg.(value & flag & info ["d"; "debug"] ~docs ~doc)
  in
  let out_arg =
    let doc = "Output file." in
    Arg.(value & opt (some string) None & info ["o"; "outfile"] ~docs ~docv:"FILE" ~doc)
  in
  let attrs_arg =
    let doc = "Attribute config files." in
    Arg.(value & opt (list file) [] & info ["attributes"] ~docs ~doc)
  in
  Term.(const mk_copts $ verbose_arg $ debug_arg $ out_arg $ attrs_arg)

let certirocq_opts_t =
  let cps_arg =
    let doc = "Use CPS translation pipeline." in
    Arg.(value & flag & info ["cps"] ~doc)
  in
  let c_args_arg =
    let doc = "Numbers of C arguments." in
    Arg.(value & opt (some int) None & info ["c-args"] ~doc)
  in
  let o_level_arg =
    let doc = "Optimization level." in
    Arg.(value & opt (some int) None & info ["O"] ~doc)
  in
  let anf_conf_arg =
    let deprecated = "Ignored: the pipeline does not read it." in
    Arg.(value & opt (some int) None & info ["anf-conf"] ~deprecated ~docv:"N")
  in
  let prefix_arg =
    let deprecated = "Ignored: CertiRocq no longer generates an FFI." in
    Arg.(value & opt (some string) None & info ["prefix"] ~deprecated ~docv:"PREFIX")
  in
  let body_name_arg =
    let doc = "Name of the toplevel function." in
    Arg.(value & opt (some string) None & info ["body-name"] ~doc)
  in
  Term.(const mk_certirocq_opts $ cps_arg $ c_args_arg $ o_level_arg $ anf_conf_arg $ prefix_arg $ body_name_arg)

let erasure_opts_t =
  let betared_arg =
    let doc = "Perform beta reduction." in
    Arg.(value & opt (some bool) None & info ["betared"] ~doc)
  in
  let unbox_arg =
    let doc = "Unbox singleton types." in
    Arg.(value & opt (some bool) None & info ["unboxing"] ~doc)
  in
  let dearg_ctors_arg =
    let doc = "Dearg constructors." in
    Arg.(value & opt (some bool) None & info ["dearg-ctors"] ~doc)
  in
  let dearg_consts_arg =
    let doc = "Dearg constants." in
    Arg.(value & opt (some bool) None & info ["dearg-consts"] ~doc)
  in
  let specialize_instances_arg =
    let doc = "Specialize functions on statically-known typeclass/dictionary arguments." in
    Arg.(value & opt (some bool) None & info ["specialize-instances"] ~doc)
  in
  let cse_arg =
    let doc = "Eliminate common subexpressions, restoring sharing that erasure drops." in
    Arg.(value & opt (some bool) None & info ["cse"] ~doc)
  in
  let lower_cofix_arg =
    let doc = "Translate cofixpoints, lazy and force to fixpoints and thunks. The correctness proofs of these passes are incomplete." in
    Arg.(value & opt (some bool) None & info ["lower-cofix"] ~doc)
  in
  Term.(const mk_erasure_opts $ betared_arg $ unbox_arg $ dearg_ctors_arg $ dearg_consts_arg $ specialize_instances_arg $ cse_arg $ lower_cofix_arg)

let s_frontend = "FRONTEND OPTIONS"

let frontend_t =
  let docs = s_frontend in
  let from_arg =
    let doc = "The frontend that reads $(i,INPUT): $(docv) is $(b,rocq), $(b,agda), $(b,lean) or $(b,lambdabox). By default it is inferred from the extension of $(i,INPUT): $(b,.v) is Rocq, $(b,.agda) and the literate $(b,.lagda)[$(b,.md)|$(b,.tex)|$(b,.rst)|$(b,.org)|$(b,.typ)|$(b,.tree)] are Agda, $(b,.lean) is Lean, and any other file is a lambda box program." in
    Arg.(value & opt (some (enum Frontend.names)) None & info ["from"] ~docs ~docv:"FRONTEND" ~doc)
  in
  let entry_arg =
    let doc = "The definition to extract from a Rocq or Lean source. Agda takes the definitions marked with a $(b,COMPILE AGDA2LAMBOX) pragma instead." in
    Arg.(value & opt (some string) None & info ["entry"] ~docs ~docv:"NAME" ~doc)
  in
  let frontend_arg =
    let doc = "Pass $(docv) to the frontend tool ($(b,rocq compile), $(b,agda2lambox), $(b,lake env lean)), e.g. $(b,--frontend-arg=-Q --frontend-arg=dir --frontend-arg=Lib). Repeatable. Without -Q, -R or -I among them, a Rocq input takes the load path of the nearest $(b,_RocqProject) or $(b,_CoqProject)." in
    Arg.(value & opt_all string [] & info ["frontend-arg"] ~docs ~docv:"ARG" ~doc)
  in
  let keep_ast_arg =
    let doc = "Also write the lambda box program of the frontend to $(docv) (and its attribute file, for Lean, to $(docv).inlinings)." in
    Arg.(value & opt (some string) None & info ["keep-ast"] ~docs ~docv:"FILE" ~doc)
  in
  let typed_arg =
    let doc = "Ask the frontend for typed lambda box. The commands whose backend needs typed lambda box ($(b,rust), $(b,elm), $(b,ast typed)) do so without it, if the frontend has typed output (Rocq, Agda)." in
    Arg.(value & flag & info ["typed"] ~docs ~doc)
  in
  let lean_config_arg =
    let doc = "The configuration of the Lean frontend, a Lean term of type $(b,Erasure.ErasureConfig) given to $(b,#erase NAME config) $(docv), e.g. $(b,'{nat := .peano}')." in
    Arg.(value & opt (some string) None & info ["lean-config"] ~docs ~docv:"TERM" ~doc)
  in
  Term.(const mk_frontend_opts $ from_arg $ entry_arg $ frontend_arg $ keep_ast_arg $ typed_arg $ lean_config_arg)

let sdocs = Manpage.s_common_options

let help man_format cmds topic = match topic with
| None -> `Help (`Pager, None)
| Some topic ->
  let topics = "topics" :: "errors" :: "warnings" :: "environment" :: cmds in
  let conv = Cmdliner.Arg.enum (List.rev_map (fun s -> (s, s)) topics) in
  let parse = Cmdliner.Arg.Conv.parser conv in
  match parse topic with
  | Error e -> `Error (false, e)
  | Ok t when t = "topics" -> List.iter print_endline topics; `Ok ()
  | Ok t when List.mem t cmds -> `Help (man_format, Some t)
  | Ok t when t = "environment" ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)
  | Ok _ ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)

let help_secs = [
  `S Manpage.s_common_options;
  `P "These options are common to all commands.";
  `S "MORE HELP";
  `P "Use $(mname) $(i,COMMAND) --help for help on a single command.";`Noblank;
  `P "Use $(mname) $(b,help environment) for help on environment variables.";
  `S Manpage.s_bugs; `P "Please report bugs at https://github.com/peregrine-project/peregrine-tool/issues.";]

let help_cmd =
  let topic =
    let doc = "The topic to get help on. $(b,topics) lists the topics." in
    Arg.(value & pos 0 (some string) None & info [] ~docv:"TOPIC" ~doc)
  in
  let doc = "display help about commands" in
  let man =
    [`S Manpage.s_description;
     `P "Prints help about commands and other subjects…";
     `Blocks help_secs; ]
  in
  let info = Cmd.info "help" ~doc ~man in
  Cmd.v info
    Term.(ret (const help $ Arg.man_format $ Term.choice_names $ topic))

let exits = Cmd.Exit.defaults @ [
  Cmd.Exit.info 1 ~doc:"on a program that is not valid or does not compile.";
  Cmd.Exit.info 10 ~max:19 ~doc:"reserved for parsing errors.";
  Cmd.Exit.info 20 ~max:29 ~doc:"reserved for compiler errors.";
  Cmd.Exit.info Frontend.tool_missing ~doc:"when the frontend tool is not on the PATH.";
  Cmd.Exit.info Frontend.tool_failed ~doc:"when the frontend fails.";
  Cmd.Exit.info Frontend.unsupported ~doc:"on options that the frontend does not support.";
]

let input_arg n =
  let doc = "The program: a lambda box program, or a Rocq, Agda or Lean source file (see $(b,--from))." in
  Arg.(required & pos n (some file) None & info [] ~docv:"INPUT" ~doc)

let man = help_secs

let compile_cmd =
  let config_file =
    let doc = "config file" in
    Arg.(required & pos 1 (some file) None & info []
           ~docv:"CONFIG_FILE" ~doc)
  in
  let doc = "Compile with a pipeline configuration file" in
  let info = Cmd.info "compile" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile $ copts_t $ frontend_t $ input_arg 0 $ config_file)

let erase_cmd =
  let doc = "Run only the frontend and write the lambda box program" in
  let info = Cmd.info "erase" ~doc ~sdocs ~man in
  Cmd.v info Term.(const erase $ copts_t $ frontend_t $ input_arg 0)

let validate_cmd =
  let config_file =
    let doc = "config file" in
    Arg.(value & opt (some file) None & info ["config"] ~doc)
  in
  let doc = "Validate program and compile configuration" in
  let info = Cmd.info "validate" ~doc ~sdocs ~man in
  Cmd.v info Term.(const validate $ copts_t $ frontend_t $ input_arg 0 $ config_file)

(* A command that compiles INPUT with the backend of [target_t] *)
let backend_cmd ?(pos=0) ?deprecated ?docs (name, doc, target_t) =
  let info = Cmd.info name ?deprecated ?docs ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_backend $ target_t $ copts_t $ erasure_opts_t $ frontend_t $ input_arg pos)

let certirocq backend =
  Term.(const (fun c -> target (backend (mk_certirocq_config c))) $ certirocq_opts_t)

let rust_t =
  let doc = "The representation of nat, positive, N and Z: " ^
    String.concat ", " (List.map (fun v -> "$(b," ^ v.rust_numbers ^ ") " ^ v.rust_verb_doc) rust_numbers) ^ "." in
  let numbers = List.map (fun v -> v.rust_numbers, v) rust_numbers in
  Term.(const rust_target $ Arg.(value & opt (enum numbers) (List.hd rust_numbers) & info ["numbers"] ~docv:"NUMBERS" ~doc))

let fuel_arg =
  let doc = "evaluator fuel" in
  Arg.(value & opt int 10000 & info ["fuel"] ~doc)

let ast_type_arg =
  let doc = "AST type" in
  Arg.(required & pos 0 (some (enum [("box", Box); ("typed", BoxTyped); ("anf", ANF); ("anfc", ANFC)])) None & info []
         ~docv:"AST_TYPE" ~doc)

let plain ?typed b = Term.const (target ?typed b)

let backends = [
  "c", "Compile to C", certirocq (fun c -> ConfigUtils.C' c);
  "wasm", "Compile to WebAssembly", certirocq (fun c -> ConfigUtils.Wasm' c);
  "llvm", "Compile to LLVM IR (textual .ll)", certirocq (fun c -> ConfigUtils.LLVM' c);
  "ocaml", "Compile to OCaml", plain (ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config');
  "cakeml", "Compile to CakeML", plain (ConfigUtils.CakeML' ConfigUtils.empty_cakeml_config');
  "rust", "Compile to Rust", rust_t;
  "elm", "Compile to Elm", plain ~typed:true (ConfigUtils.Elm' ConfigUtils.empty_elm_config');
  "lean", "Compile to Lean 4", plain (ConfigUtils.Lean' ConfigUtils.empty_lean_config');
  "fsharp", "Compile to F# (experimental)", plain (ConfigUtils.FSharp' ConfigUtils.empty_fsharp_config');
  "koka", "Compile to Koka (experimental)", plain (ConfigUtils.Koka' ConfigUtils.empty_koka_config');
  "koka-typed", "Compile to typed Koka (experimental); untyped input is typed by Hindley-Milner inference", plain ~typed:true (ConfigUtils.KokaTyped' ConfigUtils.empty_koka_config');
  "koka-typed-int", "Compile to typed Koka with nat on Koka's int (experimental)", Term.const koka_typed_int_target;
  "eval", "Evaluate the program with the lambda box interpreter", Term.(const eval_target $ certirocq_opts_t $ fuel_arg);
]

(* The verbs of the representations of numbers in Rust other than the
   default, before `rust --numbers` *)
let rust_aliases =
  List.tl rust_numbers |> List.map (fun v ->
    let deprecated = "Use $(b,rust --numbers=" ^ v.rust_numbers ^ ") instead." in
    backend_cmd ~deprecated ~docs:Manpage.s_none
      (v.rust_verb_name, "Compile to Rust, with nat/positive/N/Z as " ^ v.rust_verb_doc, Term.const (rust_target v)))

let ast_cmd =
  backend_cmd ~pos:1 ("ast", "Print an intermediate representation", Term.(const ast_target $ certirocq_opts_t $ ast_type_arg))

let main_cmd =
  let doc = "Compile Rocq, Agda and Lean programs, through LambdaBox, to C, WebAssembly, OCaml, Rust and more" in
  let man = help_secs in
  let info = Cmd.info "peregrine" ~version ~doc ~sdocs ~man ~exits in
  let default = Term.(ret (const (fun _ -> `Help (`Pager, None)) $ copts_t)) in
  Cmd.group info ~default
    (compile_cmd :: erase_cmd :: List.map backend_cmd backends @ rust_aliases @ [ast_cmd; validate_cmd; help_cmd])

let () = exit (Cmd.eval main_cmd)
