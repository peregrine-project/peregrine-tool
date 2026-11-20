open Cmdliner
open Compile
open Common

let version = "0.0.1"

let s_passes = "PASS OPTIONS"
let s_certirocq = "CERTIROCQ OPTIONS"

let last l = match List.rev l with x :: _ -> Some x | [] -> None

(* An optional pass: --NAME and --no-NAME (also under the permanent
   [aliases]), the last one wins. [old] is the deprecated BOOL option of the
   pass, before the pass options were made uniform; --NAME and --no-NAME win
   over it. *)
let pass_arg ?(aliases=[]) ?old name doc =
  let docs = s_passes in
  let names = name :: aliases in
  let doc = Printf.sprintf "%s $(b,--no-%s) disables it." doc name in
  (* --no-NAME is documented with --NAME *)
  let flags = Arg.(value & vflag_all []
                     [true, info names ~docs ~doc;
                      false, info (List.map (fun n -> "no-" ^ n) names) ~docs:Manpage.s_none]) in
  match old with
  | None -> Term.(const last $ flags)
  | Some o ->
    let deprecated = Printf.sprintf "Use $(b,--%s) or $(b,--no-%s) instead." name name in
    let old = Arg.(value & opt_all bool [] & info [o] ~docs ~docv:"BOOL" ~deprecated) in
    Term.(const (fun n o -> match last n with Some _ as r -> r | None -> last o) $ flags $ old)

(* -O LEVEL. The default pass set (see [mk] below) is on unless -O0. -O2 is a
   deprecated alias of the default, and -O1, the former intermediate level, is
   rejected. normalize_argv turns a bare -O, the default, into -O default. *)
type level = O0 | Default | O2

let level_conv =
  let parser = function
    | "0" -> Ok O0
    | "default" -> Ok Default
    | "2" -> Ok O2
    | "1" -> Error "-O1 was removed: there is no intermediate level any more. \
                    The optional passes of the default are on unless -O0, and \
                    each pass has its own option, e.g. -O0 --unwrap-fixpoints \
                    or --no-lift-constants."
    | v -> Error (Printf.sprintf "invalid value '%s', expected 0 (-O0 turns the \
                                  optional passes off)" v) in
  let pp ppf l = Format.pp_print_string ppf
      (match l with O0 -> "0" | Default -> "default" | O2 -> "2") in
  Arg.Conv.make ~docv:"LEVEL" ~parser ~pp ()

let passes_t =
  let docs = s_passes in
  let level_arg =
    let doc = "$(b,-O0) (or $(b,-O 0)) turns off the optional passes that \
               are on by default: $(b,--inline-recursors \
               --inline-standard-constants --beta-reduce --unwrap-fixpoints \
               --hoist-case-lambdas --drop-identity-matches \
               --inline-atomic-lets --lift-constants). Without it they all \
               run. A pass's own option overrides the default and $(b,-O0), \
               whatever the order, e.g. $(b,--no-lift-constants) or \
               $(b,-O0 --beta-reduce). $(b,-O) alone selects the default, as \
               does $(b,-O2), which is deprecated; $(b,-O1) was removed. The \
               last $(b,-O) wins. The passes a backend always runs or cannot \
               run are not affected. For CertiRocq's optimization level, \
               formerly $(b,-O), see $(b,--certirocq-O)." in
    Arg.(value & opt_all level_conv [] & info ["O"] ~docs ~docv:"LEVEL" ~doc)
  in
  let lbox_opts_arg =
    Arg.(value & flag & info ["lbox-opts"] ~docs ~deprecated:"Its passes are on by default; with $(b,-O0), use $(b,--unwrap-fixpoints --hoist-case-lambdas --drop-identity-matches --inline-atomic-lets --inline-standard-constants) instead.")
  in
  let lbox what = what ^ " A lambda-box simplification of ELboxOpts.v, as Rocq's \
                           extraction does in Mlutil; it runs after inlining and \
                           beta reduction, for every backend. Well-formedness \
                           and evaluation preservation are proved (ELboxOptsWf.v, \
                           ELboxOptsSim*.v). On by default." in
  let inline_recursors = pass_arg "inline-recursors"
      "Inline the recursors of the program: every constant \
       $(i,I)_rect or $(i,I)_rec whose inductive $(i,I) is declared \
       in the same module is added to the inlinings, exactly as if \
       an attribute file listed it (see --attributes). Rocq's own \
       extraction always does this. Combine with $(b,--beta-reduce) to \
       reduce the inlined recursors to direct recursion. On by default." in
  let beta_reduce = pass_arg "beta-reduce" ~old:"betared"
      "Beta-reduce. On by default." in
  let unbox = pass_arg "unbox" ~old:"unboxing"
      "Unbox singleton types." in
  let dearg_constants = pass_arg "dearg-constants" ~old:"dearg-consts"
      "Trim the dearging masks of constants (on by default for the backends \
       that support it)." in
  let specialize_instances = pass_arg "specialize-instances"
      "Specialize functions on statically-known typeclass/dictionary arguments." in
  let share_common_subterms = pass_arg "share-common-subterms" ~aliases:["cse"]
      "Eliminate common subexpressions, restoring sharing that erasure drops." in
  let lift_constants = pass_arg "lift-constants"
      "Lift closed constructor values (e.g. nat literals) to shared global \
       constants. On by default." in
  let unwrap_fixpoints = pass_arg "unwrap-fixpoints" ~old:"lbox-fix-eta" (lbox
      "Fixpoint eta-hoisting: (fun xs => (fix F ..) xs) becomes the fixpoint, \
       where an argument may also be a box passed for a dead parameter.") in
  let hoist_case_lambdas = pass_arg "hoist-case-lambdas" ~old:"lbox-case-fun" (lbox
      "Case/function permutation: match x with C => fun y => e becomes \
       fun y => match x with C => e.") in
  let drop_identity_matches = pass_arg "drop-identity-matches" ~old:"lbox-case-id" (lbox
      "Identity cases: match e with C xs => C xs becomes e.") in
  let inline_atomic_lets = pass_arg "inline-atomic-lets" ~old:"lbox-let-fun" (lbox
      "Atomic lets and applied lets: let z := a in e becomes e[a/z] for a \
       variable, box, constant or constant constructor a, (let z := v in f) b \
       becomes let z := v in f b, (fun y => e) b becomes e[b/y] and arguments \
       are pushed into the branches of an applied match, for such atomic \
       arguments b.") in
  let inline_standard_constants = pass_arg "inline-standard-constants"
      "Inline the constants that Rocq's extraction always inlines (its \
       manual inline set): andb, orb, proj1_sig, eq_rect_r, eq_rec_r, \
       well_founded_induction, well_founded_induction_type, Fix, Fix_F \
       and Acc_iter of Corelib.Init, as far as the program uses them and \
       they are not remapped. They are added to the inlinings exactly as \
       if an attribute file listed them, so this uses the verified \
       inlining pass (AutoInlining.v). On by default." in
  let inline_small_constants = pass_arg "inline-small-constants"
      "Inline every small constant: one whose body contains no fixpoint, \
       is a function or a constructor value (so that no computation is \
       duplicated or moved), and has size below $(b,--inline-size-limit), \
       measured after inlining the constants already selected (see \
       theories/AutoInlining.v for the measure, which follows ml_size of \
       Rocq's extraction). Remapped constants, the main constant and \
       those given by $(b,--no-inline) are never selected. Uses the verified \
       inlining pass; combine with $(b,--beta-reduce) and $(b,--iota-reduce). \
       Off by default." in
  let inline_size_limit =
    let doc = "Size limit of $(b,--inline-small-constants): constants of size \
               strictly below $(docv) are inlined." in
    Arg.(value & opt int 12 & info ["inline-size-limit"] ~docs ~docv:"N" ~doc)
  in
  let no_inline =
    let doc = "Never select the constant $(docv) (a full kernel name such \
               as Corelib.Init.Datatypes.andb) for \
               $(b,--inline-standard-constants) or $(b,--inline-small-constants). \
               Repeatable. Inlinings requested by attribute files or \
               $(b,--inline-recursors) are not affected." in
    Arg.(value & opt_all string [] & info ["no-inline"] ~docs ~docv:"NAME" ~doc)
  in
  let iota_reduce = pass_arg "iota-reduce"
      "Generalised iota reduction (ELboxOpts.v, as in Mlutil of Rocq's \
       extraction): a match on a constructor application becomes its \
       branch, with the arguments bound by lets (atomic arguments are \
       substituted); a match on a let is pushed under the let; a match on \
       a match all of whose branches end in constructors is pushed into \
       these branches, unless that would duplicate a large branch. Runs \
       after inlining and beta reduction and before the other lambda-box \
       simplifications and $(b,--lift-constants), for every backend. \
       Well-formedness and evaluation preservation are proved without \
       axioms. Off by default." in
  let mk level lbox_opts ir br ub dc si cse lc fe cf ci lf std small limit noinl iota =
    if List.mem O2 level then
      prerr_endline "peregrine: -O2 is deprecated: its passes are the default (-O0 turns them off).";
    let optimize = last level <> Some O0 in
    (* A pass not set explicitly is on if it is in the default pass set and
       not under -O0, and otherwise off. Beta reduction and constant lifting
       are left to the configuration file, then to the default pass set
       ([optimize], see mk_erasure_config in compile.ml), then to the backend.
       The deprecated --lbox-opts turns on the former -O1 passes, also under
       -O0. *)
    let on o = Option.value ~default:optimize o in
    let o1 o = Option.value ~default:(optimize || lbox_opts) o in
    let off o = Option.value ~default:false o in
    { optimize;
      inline_recursors = on ir; beta_reduce = br; unbox = ub;
      dearg_constants = dc; specialize_instances = si;
      share_common_subterms = cse; lift_constants = lc;
      unwrap_fixpoints = o1 fe; hoist_case_lambdas = o1 cf;
      drop_identity_matches = o1 ci; inline_atomic_lets = o1 lf;
      iota_reduce = off iota;
      inline_standard_constants = o1 std; inline_small_constants = off small;
      inline_size_limit = limit; no_inline = noinl }
  in
  Term.(const mk $ level_arg $ lbox_opts_arg $ inline_recursors $ beta_reduce $ unbox
        $ dearg_constants $ specialize_instances $ share_common_subterms $ lift_constants
        $ unwrap_fixpoints $ hoist_case_lambdas $ drop_identity_matches $ inline_atomic_lets
        $ inline_standard_constants $ inline_small_constants $ inline_size_limit $ no_inline
        $ iota_reduce)

(* The forms --specialize-instances=BOOL and --cse=BOOL (or with BOOL as the
   next argument) of before the pass options were flags, deprecated: they
   become --X or --no-X, so the last of them wins. A bare -O becomes
   -Odefault. *)
let normalize_argv argv =
  let bool_flags = ["specialize-instances"; "cse"] in
  let flag n b = if b then "--" ^ n else "--no-" ^ n in
  let warn n v =
    Printf.eprintf "peregrine: option '--%s %s' deprecated, use '%s' instead.\n%!"
      n v (flag n (v = "true")) in
  let is_bool v = v = "true" || v = "false" in
  (* Digits are taken as a level, so that -O 3 is rejected as one *)
  let is_level v =
    v <> "" && String.for_all (fun c -> c >= '0' && c <= '9') v in
  let rec go = function
    | [] -> []
    | "--" :: rest -> "--" :: rest
    (* A bare -O is the default; cmdliner would take the next argument as its
       value, so it is given one. *)
    | "-O" :: rest when (match rest with
        | v :: _ -> not (v = "default" || is_level v)
        | [] -> true) ->
      "-Odefault" :: go rest
    | a :: rest ->
      match String.index_opt a '=' with
      | Some i when i > 2 && String.sub a 0 2 = "--"
                    && List.mem (String.sub a 2 (i - 2)) bool_flags
                    && is_bool (String.sub a (i + 1) (String.length a - i - 1)) ->
        let n = String.sub a 2 (i - 2) and v = String.sub a (i + 1) (String.length a - i - 1) in
        warn n v; flag n (v = "true") :: go rest
      | None when String.length a > 2 && String.sub a 0 2 = "--"
                  && List.mem (String.sub a 2 (String.length a - 2)) bool_flags ->
        (match rest with
         | v :: rest' when is_bool v ->
           let n = String.sub a 2 (String.length a - 2) in
           warn n v; flag n (v = "true") :: go rest'
         | _ -> a :: go rest)
      | _ -> a :: go rest
  in
  match Array.to_list argv with
  | [] -> argv
  | prog :: args -> Array.of_list (prog :: go args)

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
  let strict_verified_arg =
    let doc = "Fail when the OCaml or CakeML backend cannot guarantee that the \
               program satisfies the precondition of verified extraction's \
               correctness theorem (for example, because it uses primitive \
               strings), instead of compiling it with a warning. \
               $(b,--no-strict-verified) (the default) only warns." in
    let flags = Arg.(value & vflag_all []
                       [true, info ["strict-verified"] ~docs ~doc;
                        false, info ["no-strict-verified"] ~docs:Manpage.s_none]) in
    Term.(const (fun l -> last l = Some true) $ flags)
  in
  Term.(const mk_copts $ verbose_arg $ debug_arg $ out_arg $ attrs_arg $ passes_t
        $ strict_verified_arg)

let certirocq_opts_t =
  let docs = s_certirocq in
  (* The pre-prefix names of the options, deprecated *)
  let old name ~docv cv =
    let deprecated = Printf.sprintf "Use $(b,--certirocq-%s) instead." name in
    Arg.(value & opt (some cv) None & info [name] ~docs ~deprecated ~docv)
  in
  let cps_arg =
    let doc = "Use CertiRocq's CPS pipeline instead of the direct-style one." in
    Arg.(value & flag & info ["certirocq-cps"] ~docs ~doc)
  in
  let old_cps_arg =
    Arg.(value & flag & info ["cps"] ~docs ~deprecated:"Use $(b,--certirocq-cps) instead.")
  in
  let c_args_arg =
    let doc = "The number of arguments of a generated C function that are passed as C arguments (the others go through the argument array)." in
    Arg.(value & opt (some int) None & info ["certirocq-c-args"] ~docs ~docv:"N" ~doc)
  in
  let o_level_arg =
    let doc = "CertiRocq's optimization level: 1 (the default) enables lambda lifting, 0 disables it. Before, this was $(b,-O) $(docv), which now turns peregrine's optional passes off ($(b,-O0))." in
    Arg.(value & opt (some int) None & info ["certirocq-O"] ~docs ~docv:"N" ~doc)
  in
  let body_name_arg =
    let doc = "Name of the toplevel function." in
    Arg.(value & opt (some string) None & info ["certirocq-body-name"] ~docs ~docv:"NAME" ~doc)
  in
  let mk cps old_cps c_args old_c_args o_level body_name old_body_name =
    let ( ||| ) a b = match a with Some _ -> a | None -> b in
    mk_certirocq_opts (cps || old_cps) (c_args ||| old_c_args) o_level (body_name ||| old_body_name)
  in
  Term.(const mk $ cps_arg $ old_cps_arg $ c_args_arg $ old "c-args" ~docv:"N" Arg.int $ o_level_arg
        $ body_name_arg $ old "body-name" ~docv:"NAME" Arg.string)

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
  `S s_passes;
  `P "These options select the optional passes of the pipeline. Every \
      command accepts them; $(b,erase) and $(b,validate) ignore them. A \
      pass is set by its last $(b,--)$(i,PASS) or $(b,--no-)$(i,PASS), \
      otherwise by its deprecated $(i,BOOL) option, otherwise by the \
      configuration file of $(b,compile), otherwise by the default pass \
      set (unless $(b,-O0)), otherwise by the backend's default. A backend that requires a pass or \
      cannot run it ignores the setting.";
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
  Cmd.v info Term.(const compile_backend $ target_t $ copts_t $ frontend_t $ input_arg pos)

let certirocq backend =
  Term.(const (fun c -> target (backend (mk_certirocq_config c))) $ certirocq_opts_t)

let rust_t =
  let doc = "The representation of nat, positive, N and Z: " ^
    String.concat ", " (List.map (fun v -> "$(b," ^ v.rust_numbers ^ ") " ^ v.rust_verb_doc) rust_numbers) ^ "." in
  let numbers = List.map (fun v -> v.rust_numbers, v) rust_numbers in
  let docs = "RUST OPTIONS" in
  let new_arg = Arg.(value & opt (some (enum numbers)) None & info ["rust-numbers"] ~docs ~docv:"NUMBERS" ~doc) in
  let old_arg = Arg.(value & opt (some (enum numbers)) None & info ["numbers"] ~docs ~docv:"NUMBERS"
                       ~deprecated:"Use $(b,--rust-numbers) instead.") in
  let pick n o = rust_target (match n, o with
      | Some v, _ | None, Some v -> v
      | None, None -> List.hd rust_numbers) in
  Term.(const pick $ new_arg $ old_arg)

let fuel_arg =
  let docs = "EVAL OPTIONS" in
  let doc = "The fuel of the evaluator." in
  let new_arg = Arg.(value & opt (some int) None & info ["eval-fuel"] ~docs ~docv:"N" ~doc ~absent:"10000") in
  let old_arg = Arg.(value & opt (some int) None & info ["fuel"] ~docs ~docv:"N"
                       ~deprecated:"Use $(b,--eval-fuel) instead.") in
  Term.(const (fun n o -> match n, o with Some f, _ | None, Some f -> f | None, None -> 10000) $ new_arg $ old_arg)

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
   default, before `rust --rust-numbers` *)
let rust_aliases =
  List.tl rust_numbers |> List.map (fun v ->
    let deprecated = "Use $(b,rust --rust-numbers=" ^ v.rust_numbers ^ ") instead." in
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

let () = exit (Cmd.eval ~argv:(normalize_argv Sys.argv) main_cmd)
