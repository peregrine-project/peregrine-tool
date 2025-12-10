open Cmdliner
open Compile
open Common

let version = "0.0.1"

let copts_t =
  let docs = Manpage.s_common_options in
  let verbose_arg =
    let doc = "Suppress informational output." in
    let quiet = Quiet, Arg.info ["q"; "quiet"] ~docs ~doc in
    let doc = "Give verbose output." in
    let verbose = Verbose, Arg.info ["v"; "verbose"] ~docs ~doc in
    Arg.(last & vflag_all [Normal] [quiet; verbose])
  in
  let debug_arg =
    let doc = "Enable debug information." in
    Arg.(value & flag & info ["d"; "debug"] ~docs ~doc)
  in
  let out_arg =
    let doc = "Output file." in
    Arg.(value & opt (some string) None & info ["o"; "outfile"] ~docs ~doc)
  in
  let wf_arg =
    let doc = "Bypass welformedness checks." in
    Arg.(value & flag & info ["bypass-wf"] ~docs ~doc)
  in
  Term.(const mk_copts $ verbose_arg $ debug_arg $ out_arg $ wf_arg)

let sdocs = Manpage.s_common_options

let help man_format cmds topic = match topic with
| None -> `Help (`Pager, None)
| Some topic ->
  let topics = "topics" :: "errors" :: "warnings" :: "environment" :: cmds in
  let conv, _ = Cmdliner.Arg.enum (List.rev_map (fun s -> (s, s)) topics) in
  match conv topic with
  | `Error e -> `Error (false, e)
  | `Ok t when t = "topics" -> List.iter print_endline topics; `Ok ()
  | `Ok t when List.mem t cmds -> `Help (man_format, Some t)
  | `Ok t when t = "environment" ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)
  | `Ok _ ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)

let help_secs = [
  `S Manpage.s_common_options;
  `P "These options are common to all commands.";
  `S "MORE HELP";
  `P "Use $(mname) $(i,COMMAND) --help for help on a single command.";`Noblank;
  `P "Use $(mname) $(b,help environment) for help on environment variables.";
  `S Manpage.s_bugs; `P "Please report bugs at https://github.com/AU-COBRA/lambda-box-extraction/issues.";]

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
  Cmd.Exit.info 10 ~max:19 ~doc:"on parsing errors.";
  Cmd.Exit.info 20 ~max:29 ~doc:"on compiler errors.";
]

let certicoq_opts_t =
  let cps_arg =
    let doc = "Use CPS translation pipeline." in
    Arg.(value & flag & info ["cps"] ~doc)
  in
  Term.(const (fun x -> mk_certicoq_opts x) $ cps_arg )

let eopts_t =
  let typed_arg =
    let doc = "Parse input as typed lambda box program." in
    Arg.(value & opt (some string) None & info ["typed"] ~doc)
  in
  let opt_arg =
    let doc = "Enable dearging optimization (only available when using --typed)." in
    Arg.(value & flag & info ["opt"] ~doc)
  in
  Term.(const mk_erasure_opts $ typed_arg $ opt_arg)

let teopts_t =
  let opt_arg =
    let doc = "Enable dearging optimization." in
    Arg.(value & flag & info ["opt"] ~doc)
  in
  Term.(const mk_typed_erasure_opts $ opt_arg)

let eval_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let anf_arg =
    let doc = "Use lambda ANF evaluator." in
    Arg.(value & flag & info ["anf"] ~doc)
  in
  let doc = "Evaluate lambda box program" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "eval" ~doc ~sdocs ~man in
  Cmd.v info Term.(const eval_box $ copts_t $ eopts_t $ certicoq_opts_t $ anf_arg $ file)

let validate_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Validate lambda box program" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "validate" ~doc ~sdocs ~man in
  Cmd.v info Term.(const validate_box $ copts_t $ eopts_t $ file)

let wasm_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box to webassembly" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "wasm" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_wasm $ copts_t $ eopts_t $ certicoq_opts_t $ file)

let c_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box to C" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "c" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_c $ copts_t $ eopts_t $ certicoq_opts_t $ file)

let anf_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box to ANF" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "anf" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_anf $ copts_t $ eopts_t $ certicoq_opts_t $ file)

let ocaml_cmd =
  let file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box to OCaml" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "ocaml" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_ocaml $ copts_t $ eopts_t $ file)

let rust_cmd =
  let file =
    let doc = "lambda box typed environment" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let attr_arg =
    let doc = "Type attributes, defaults to \"#[derive(Debug, Clone)]\"" in
    Arg.(value & opt (some string) None & info ["attr"] ~doc)
  in
  let top_pre_arg =
    let doc = "File preamble" in
    Arg.(value & opt (some string) None & info ["top-preamble"] ~doc)
  in
  let prog_pre_arg =
    let doc = "Program preamble" in
    Arg.(value & opt (some string) None & info ["prog-preamble"] ~doc)
  in
  let doc = "Compile lambda box to rust" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "rust" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_rust $ copts_t $ teopts_t $ top_pre_arg $ prog_pre_arg $ attr_arg $ file)

let elm_cmd =
  let file =
    let doc = "lambda box typed environment" in
    Arg.(required & pos 0 (some file) None  & info []
           ~docv:"FILE" ~doc)
  in
  let top_pre_arg =
    let doc = "File preamble" in
    Arg.(value & opt (some string) None & info ["top-preamble"] ~doc)
  in
  let doc = "Compile lambda box to elm" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "elm" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_elm $ copts_t $ teopts_t $ top_pre_arg $ file)

let main_cmd =
  let doc = "a compiler for lambda box to webassembly" in
  let man = help_secs in
  let info = Cmd.info "lbox" ~version ~doc ~sdocs ~man ~exits in
  let default = Term.(ret (const (fun _ -> `Help (`Pager, None)) $ copts_t)) in
  Cmd.group info ~default [eval_cmd; validate_cmd; wasm_cmd; c_cmd; anf_cmd; ocaml_cmd; rust_cmd; elm_cmd; help_cmd]

let () = exit (Cmd.eval main_cmd)
