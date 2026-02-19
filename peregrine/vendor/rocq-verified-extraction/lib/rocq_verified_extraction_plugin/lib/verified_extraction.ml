type inductive_mapping = Kernames.inductive * (string * int list) (* Target inductive type and mapping of constructor names to constructor tags *)
type inductives_mapping = inductive_mapping list

type unsafe_passes = 
  { cofix_to_lazy : bool;
    inlining : bool;
    unboxing : bool;
    betared : bool }

type erasure_configuration = { 
  enable_unsafe : unsafe_passes;
  enable_typed_erasure : bool;
  inlined_constants : Kernames.KernameSet.t }

type prim_def =
| Global of string * string
| Primitive of string * int
| Erased

type prim = Kernames.kername * prim_def

type primitives = prim list

type malfunction_pipeline_config = { 
  erasure_config : erasure_configuration;
  reorder_constructors : inductives_mapping;
  prims : primitives }

type program_type =
  | Standalone of bool (* Link statically with Rocq's libraries *)
  | Plugin

type unsafe_pass = 
  | CoFixToLazy
  | Inlining
  | Unboxing
  | BetaRed

type malfunction_command_args =
  | Unsafe of unsafe_pass list
  | Verbose
  | Time
  | Typed
  | BypassQeds
  | ProgramType of program_type
  | Load
  | Run
  | Format
  | Optimize

type malfunction_plugin_config = 
  { malfunction_pipeline_config : malfunction_pipeline_config;
    bypass_qeds : bool;
    time : bool;
    verbose : bool;
    program_type : program_type option;
    load : bool;
    run : bool;
    loc : Loc.t option;
    format : bool;
    optimize : bool;
    use_opam_env : bool }

let debug_extract = CDebug.create ~name:"verified-extraction" ()
let debug = debug_extract

let get_stringopt_option key =
  let open Goptions in
  match get_option_value key with
  | Some get -> fun () ->
      begin match get () with
      | StringOptValue b -> b
      | _ -> assert false
      end
  | None ->
    (declare_stringopt_option_and_ref ~key ~value:None ()).get

let get_bool_option ?(default=false) key =
  let open Goptions in
  match get_option_value key with
  | Some get -> fun () ->
      begin match get () with
      | BoolValue b -> b
      | _ -> assert false
      end
  | None ->
    (declare_bool_option_and_ref ~key ~value:default ()).get

let get_build_dir_opt =
  get_stringopt_option ["Verified"; "Extraction"; "Build"; "Directory"]

let get_opam_path_opt =
  get_stringopt_option ["Verified"; "Extraction"; "Opam"; "Path"]

let get_use_opam_opt =
  get_bool_option ~default:true ["Verified"; "Extraction"; "Use"; "Opam"]

(* When building standalone programs still relying on Rocq's/MetaRocq's FFIs, use these packages for linking *)
let statically_linked_pkgs =
  ["rocq-runtime.boot";
    "rocq-runtime.clib";
    "rocq-runtime.config";
    "rocq-runtime";
    "rocq-runtime.engine";
    "rocq-runtime.gramlib";
    "rocq-runtime.interp";
    "rocq-runtime.kernel";
    "rocq-runtime.lib";
    "rocq-runtime.library";
    "rocq-runtime.parsing";
    "rocq-runtime.pretyping";
    "rocq-runtime.printing";
    "rocq-runtime.proofs";
    "rocq-runtime.stm";
    "rocq-runtime.sysinit";
    "rocq-runtime.tactics";
    "rocq-runtime.toplevel";
    "rocq-runtime.vernac";
    "rocq-runtime.vm";
    "rocq-metarocq-template-ocaml.plugin";
    "dynlink";
    "findlib";
    "findlib.dynload";
    "findlib.internal";
    "stdlib-shims";
    "str";
    "threads";
    "threads.posix";
    "unix";
    "zarith"]

let notice opts pp = 
  if opts.verbose then
    Feedback.msg_notice ?loc:opts.loc (pp ())
  else ()

let time prefix f x =
  let start = Unix.gettimeofday () in
  let res = f x in
  let stop = Unix.gettimeofday () in
  let () = Feedback.msg_info Pp.(prefix ++ str " executed in: " ++ Pp.real (stop -. start) ++ str "s") in
  res

let time opts = 
  if opts.time then (fun label fn arg -> time label fn arg) 
  else fun _label fn arg -> fn arg

(* Separate registration of primitive extraction *)

type package = string (* Findlib package names to link for external references *)

let globref_of_qualid ?loc (gr : Libnames.qualid) : Names.GlobRef.t  =
  match Constrintern.locate_reference gr with
  | exception Not_found -> CErrors.user_err ?loc Pp.(Libnames.pr_qualid gr ++ str " not found.")
  | None -> CErrors.user_err ?loc Pp.(Libnames.pr_qualid gr ++ str " not found.")
  | Some g -> g
    
let quoted_globref_of_qualid ~loc (gr : Libnames.qualid) : Kernames.global_reference =
  Metarocq_template_plugin.Ast_quoter.quote_global_reference (globref_of_qualid ~loc gr)

let constant_of_qualid ~loc (gr : Libnames.qualid) : Kernames.kername =
  match quoted_globref_of_qualid ~loc gr with
  | Kernames.ConstRef kn -> kn
  | Kernames.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a variable. Only constants can be realized in Malfunction.")
  | Kernames.IndRef(i) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found an inductive type. Only constants can be realized in Malfunction.")
  | Kernames.ConstructRef(_, _) -> CErrors.user_err ~loc Pp.(str "Expected a constant but found a constructor. Only constants can be realized in Malfunction. ")
    
let inductive_of_qualid ~loc (gr : Libnames.qualid) : Kernames.inductive =
  match quoted_globref_of_qualid ~loc gr with
  | Kernames.ConstRef kn -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constant. Only inductives can be translated in Malfunction.")
  | Kernames.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a variable. Only constants can be translated in Malfunction.")
  | Kernames.IndRef(i) -> i
  | Kernames.ConstructRef(_, _) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constructor. Only constants can be translated in Malfunction. ")
  
let extract_constant (gr : Kernames.kername) (s : string) : prim =
  let s = String.split_on_char '.' s in 
  let label, module_ = CList.sep_last s in
  let module_ =  (String.concat "." module_) in
  (gr, Global (module_, label))
  
let extract_primitive (gr : Kernames.kername) (symb : string) (arity : int) : prim =
  (gr, Primitive (symb, arity))

let extract_inductive (gr : Kernames.inductive) (cstrs : string * int list) : inductive_mapping =
  (gr, cstrs)

let extract_inline (gr : Kernames.kername) : Kernames.KernameSet.t =
  Kernames.KernameSet.singleton gr
  
(* Extract Inductive *)
let global_inductive_registers = 
  Summary.ref ([] : inductives_mapping) ~name:"Verified Extraction Inductive Registration"

let global_inductive_registers_name = "verified-extraction-inductive-registration"

let cache_inductive_registers inds =
  let inds' = !global_inductive_registers in
  global_inductive_registers := inds @ inds'

let global_inductive_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_inductive_registers_name
    ~cache:(fun r -> cache_inductive_registers r)
    ~subst:None)

let register_inductives (inds : inductives_mapping) : unit =
  Lib.add_leaf (global_inductive_registers_input inds)

let get_global_inductives_mapping () = !global_inductive_registers

(* Extract Inline *)

let global_inlining_registers = 
  Summary.ref ~name:"Verified Extraction Inlining Registration" Kernames.KernameSet.empty
  
let global_inlining_registers_name = "verified-extraction-inlining-registration"

let cache_inlining_registers csts =
  let csts' = !global_inlining_registers in
  global_inlining_registers := Kernames.KernameSet.union csts csts'

let global_inlining_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_inlining_registers_name
    ~cache:(fun r -> cache_inlining_registers r)
    ~subst:None)

let register_inlines (csts : Kernames.kername list) : unit =
  Lib.add_leaf (global_inlining_registers_input (Kernames.KernameSetProp.of_list csts))

let get_global_inlinings_mapping () = !global_inlining_registers


(* Primitives / Extract Constant *)
let global_registers = 
  Summary.ref (([], []) : prim list * package list) ~name:"Verified Extraction Registration"

let global_registers_name = "verified-extraction-registration"

let cache_registers (prims, packages) =
  let (prims', packages') = !global_registers in
  global_registers := (prims @ prims', packages @ packages')

let global_registers_input = 
  let open Libobject in 
  declare_object 
    (global_object_nodischarge global_registers_name
    ~cache:(fun r -> cache_registers r)
    ~subst:None)

let register (prims : prim list) (packages : package list) : unit =
  Lib.add_leaf (global_registers_input (prims, packages))

let get_global_prims () = fst !global_registers
let get_global_packages () = snd !global_registers

let pr_char c = Pp.str (Char.escaped c)

let bytes_of_list l =
  let bytes = Bytes.create (List.length l) in
  let rec fill acc = function
    | [] -> bytes
    | c :: cs ->
      Bytes.set bytes acc c;
      fill (1 + acc) cs
  in fill 0 l

let make_unsafe_flags b = 
  { cofix_to_lazy = b; 
    inlining = b;
    unboxing = b;
    betared = b }

let default_unsafe_flags = make_unsafe_flags false
let all_unsafe_flags = make_unsafe_flags true

let default_erasure_config inlined_constants = 
  { enable_unsafe = default_unsafe_flags; enable_typed_erasure = false;
    inlined_constants }

let default_malfunction_config inductives_mapping inlined_constants prims = 
  { erasure_config = default_erasure_config inlined_constants; reorder_constructors = inductives_mapping; prims }

let set_unsafe_flag fl = function
| CoFixToLazy -> { fl with cofix_to_lazy = true }
| Inlining -> { fl with inlining = true }
| Unboxing -> { fl with unboxing = true }
| BetaRed -> { fl with betared = true }

let make_options loc l =
  let inductives_mapping = get_global_inductives_mapping () in
  let inlining = get_global_inlinings_mapping () in
  let prims = get_global_prims () in
  let default = {
    malfunction_pipeline_config = default_malfunction_config inductives_mapping inlining prims;
    bypass_qeds = false; time = false; program_type = None; load = false; run = false;
    verbose = false; loc; format = false; optimize = false;
    use_opam_env = get_use_opam_opt () }  
  in
  let parse_unsafe_flags unsafe l = 
    match l with
    | [] -> all_unsafe_flags
    | flags -> List.fold_left set_unsafe_flag unsafe flags
  in
  let rec parse_options opts l = 
    match l with
    | [] -> opts
    | Unsafe flags :: l ->
      let erasure_config = opts.malfunction_pipeline_config.erasure_config in
      parse_options { opts with 
      malfunction_pipeline_config = { opts.malfunction_pipeline_config with erasure_config = 
      { erasure_config with enable_unsafe = parse_unsafe_flags erasure_config.enable_unsafe flags } } } l
    | Typed :: l -> parse_options { opts with 
      malfunction_pipeline_config = { opts.malfunction_pipeline_config with erasure_config = 
      { opts.malfunction_pipeline_config.erasure_config with enable_typed_erasure = true } } } l
    | BypassQeds :: l -> parse_options { opts with bypass_qeds = true } l
    | Time :: l -> parse_options { opts with time = true } l
    | Verbose :: l -> parse_options { opts with verbose = true } l
    | ProgramType t :: l -> parse_options { opts with program_type = Some t } l
    | Load :: l -> parse_options { opts with load = true } l
    | Run :: l -> parse_options { opts with run = true } l
    | Format :: l -> parse_options { opts with format = true } l
    | Optimize :: l -> parse_options { opts with optimize = true } l
  in 
  let check_options opts =
    match opts.program_type with
    | Some Plugin -> if opts.run then { opts with load = true } else opts
    | _ -> opts
  in
  let opts = parse_options default l in
  check_options opts

type line = 
| EOF
| Info of string
| Error of string

let read_line stdout stderr =
  try Info (input_line stdout)
  with End_of_file -> 
    try Error (input_line stderr)
  with End_of_file -> EOF

let push_line buf line =
  Buffer.add_string buf line; 
  Buffer.add_string buf "\n"

let string_of_buffer buf = Bytes.to_string (Buffer.to_bytes buf)

let execute cmd =
  debug Pp.(fun () -> str "Executing: " ++ str cmd ++ str " in environemt: " ++ 
    prlist_with_sep spc str (Array.to_list (Unix.environment ())));
  let (stdout, stdin, stderr) = Unix.open_process_full cmd (Unix.environment ()) in
  let continue = ref true in
  let outbuf, errbuf = Buffer.create 100, Buffer.create 100 in
  let push_info = push_line outbuf in
  let push_error = push_line errbuf in
  while !continue do
    match read_line stdout stderr with
    | EOF -> debug Pp.(fun () -> str "Program terminated"); continue := false
    | Info s -> push_info s
    | Error s -> push_error s
  done;
  let status = Unix.close_process_full (stdout, stdin, stderr) in
  status, string_of_buffer outbuf, string_of_buffer errbuf

let run_command opts cmd = 
  let status, out, err = execute cmd in
  match status with
  | Unix.WEXITED 0 -> debug Pp.(fun () -> str "Execution result is" ++ spc () ++ str out);
    String.trim out
  | _ -> 
    CErrors.user_err ?loc:opts.loc Pp.(str "Execution of" ++ spc () ++ str cmd ++ spc () ++ str "failed:" ++ fnl () ++
      str out ++ str err)

let opam_command cmd = 
  match get_opam_path_opt () with
  | Some s -> s ^ " exec -- " ^ cmd
  | None -> cmd
      
let execute opts cmd =
  let status, out, err = execute cmd in
  match status with
  | Unix.WEXITED 0 -> out, err
  | Unix.WEXITED n -> 
    CErrors.user_err ?loc:opts.loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++
      str"exited with code " ++ int n ++ str "." ++ fnl () ++
      str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)
  | Unix.WSIGNALED n | Unix.WSTOPPED n -> 
    CErrors.user_err ?loc:opts.loc Pp.(str"Command" ++ spc () ++ str cmd ++ spc () ++ 
    str"was signaled with code " ++ int n ++ str"." ++ fnl () ++
    str"stdout: " ++ spc () ++ str out ++ fnl () ++ str "stderr: " ++ str err)

let get_prefix () = 
  match get_build_dir_opt () with
  | None -> "."
  | Some s -> s 

let build_fname f = 
  Filename.concat (get_prefix ()) f

let increment_subscript id =
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if Util.is_digit c then
      if Int.equal (Char.code c) (Char.code '9') then begin
        assert (carrypos>0);
        add (carrypos-1)
      end
      else begin
        let newid = Bytes.of_string id in
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid carrypos (Char.chr (Char.code c + 1));
        newid
      end
    else begin
      let newid = Bytes.of_string (id^"0") in
      if carrypos < len-1 then begin
        Bytes.fill newid (carrypos+1) (len-1-carrypos) '0';
        Bytes.set newid (carrypos+1) '1'
      end;
      newid
    end
  in String.of_bytes (add (len-1))

let next_string_away_from s bad =
  let rec name_rec s = if bad s then name_rec (increment_subscript s) else s in
  name_rec s

type malfunction_program_type = 
  | Standalone_binary
  | Shared_library of string * string

type plugin_function = Obj.t

let register_plugins = Summary.ref ~name:"verified-extraction-plugins" (CString.Map.empty : plugin_function CString.Map.t)

let cache_plugin (name, fn) = 
  register_plugins := CString.Map.add name fn !register_plugins
  
let plugin_input =
  let open Libobject in 
  declare_object 
    (global_object_nodischarge "verified-extraction-plugins"
    ~cache:(fun r -> cache_plugin r)
    ~subst:None)
  
let register_plugin name fn : unit =
  Lib.add_leaf (plugin_input (name, fn))
  
module Reify =
struct

  type reifyable_value_type =
  | IsInductive of Names.inductive * UVars.Instance.t * Constr.t list
  | IsPrimitive of Names.Constant.t * UVars.Instance.t * Constr.t list
  
  type reifyable_type = 
  | IsThunk of reifyable_value_type
  | IsValue of reifyable_value_type

  let type_of_reifyable_type = function
    | IsInductive (hd, u, args) -> Term.applistc (Constr.mkIndU ((hd, u))) args
    | IsPrimitive (c, u, args) -> Term.applistc (Constr.mkConstU ((c, u))) args

  let pr_reifyable_value_type env sigma ty =
    Printer.pr_constr_env env sigma (type_of_reifyable_type ty)

  let pr_reifyable_type env sigma = function
    | IsThunk ty -> Pp.(str"unit -> " ++ pr_reifyable_value_type env sigma ty)
    | IsValue ty -> pr_reifyable_value_type env sigma ty

  let find_nth_constant n ar =
    let open Inductiveops in
    let rec aux i const = 
      if Array.length ar <= i then raise Not_found
      else if CList.is_empty ar.(i).cs_args then  (* FIXME lets in constructors *)
        if const = n then i 
        else aux (i + 1) (const + 1)
      else aux (i + 1) const
    in aux 0 0

  let find_nth_non_constant n ar =
    let open Inductiveops in
    let rec aux i nconst = 
      if Array.length ar <= i then raise Not_found
      else if not (CList.is_empty ar.(i).cs_args) then 
        if nconst = n then i
        else aux (i + 1) (nconst + 1)
      else aux (i + 1) nconst
    in aux 0 0
    
  let invalid_type ?loc env sigma ty = 
    CErrors.user_err ?loc
      Pp.(str"Cannot reify values of non-inductive or non-primitive type: " ++ 
          Printer.pr_econstr_env env sigma ty)
    
  let check_reifyable_value_type ?loc env sigma ty =
    (* We might have bound universes though. It's fine! *)
    try let (hd, u), args = Inductiveops.find_inductive env sigma ty in
      IsInductive (hd, EConstr.EInstance.kind sigma u, List.map (EConstr.to_constr sigma) args)
    with Not_found -> 
      let hnf = Reductionops.whd_all env sigma ty in
      let hd, args = EConstr.decompose_app sigma hnf in
      match EConstr.kind sigma hd with
      | Const (c, u) when Environ.is_primitive_type env c -> 
        IsPrimitive (c, EConstr.EInstance.kind sigma u, CArray.map_to_list EConstr.Unsafe.to_constr args)
      | _ -> invalid_type ?loc env sigma hnf

  let check_reifyable_value ?loc env sigma c =
    check_reifyable_value_type ?loc env sigma (Retyping.get_type_of env sigma c)
  
  let check_reifyable_thunk_or_value_type ?loc env sigma ty =
    debug Pp.(fun () -> str "Checking reifyability of " ++ Printer.pr_econstr_env env sigma ty);
    match EConstr.kind sigma ty with
    | Constr.Prod (na, dom, codom) -> 
      (match Inductiveops.find_inductive env sigma dom with
      | exception Not_found -> invalid_type ?loc env sigma dom
      | (hd, u), args -> 
        if Environ.QGlobRef.equal env (Rocqlib.lib_ref "core.unit.type") (IndRef hd) then
          let tt = Rocqlib.lib_ref "core.unit.tt" in
          let sigma, ttc = Evd.fresh_global env sigma tt in
          IsThunk (check_reifyable_value_type ?loc env sigma (EConstr.Vars.subst1 ttc codom))
        else invalid_type ?loc env sigma dom)
    | _ -> IsValue (check_reifyable_value_type ?loc env sigma ty)
  
  let check_reifyable_thunk_or_value ?loc env sigma v =
    check_reifyable_thunk_or_value_type ?loc env sigma (Retyping.get_type_of env sigma v)
  
  let ill_formed env sigma ty =
    match ty with
    | IsInductive _ -> 
      CErrors.anomaly ~label:"verified-extraction-reify-ill-formed"
      Pp.(str "Ill-formed inductive value representation in MetaRocq's Extraction reification for type " ++
        pr_reifyable_value_type env sigma ty)
    | IsPrimitive _ ->
      CErrors.anomaly ~label:"verified-extraction-reify-ill-formed"
      Pp.(str "Ill-formed primitive value representation in MetaRocq's Extraction reification for type " ++
        pr_reifyable_value_type env sigma ty)

  (* let ocaml_get_boxed_ordinal v = 
    (* tag is the header of the object *)
    let tag = Array.unsafe_get (Obj.magic v : Obj.t array) (-1) in
    (* We turn it into an ocaml int usable for arithmetic operations *)
    let tag_int = (Stdlib.Int.shift_left (Obj.magic (Obj.repr tag)) 1) + 1 in
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml tag: %i" (Obj.tag tag)));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal int: %u" tag_int));
    Feedback.msg_debug (Pp.str (Printf.sprintf "Ocaml get_boxed_ordinal ordinal: %u" (tag_int land 255)));
    tag_int land 255 *)

  let apply_reordering hd m cstrs =
    try
      let find_ind_ord (ind, (na, tags)) =
        if Kernames.eq_inductive_def ind hd then
          Some (Array.of_list (List.map (fun i -> cstrs.(i)) tags))
        else None
      in
      CList.find_map_exn find_ind_ord m
    with Not_found -> cstrs

  let find_reverse_mapping hd m cstr =
    try
      let find_ind_ord (ind, (na, tags)) =
        if Kernames.eq_inductive_def ind hd then
          Some (CList.index0 Int.equal cstr tags)
        else None
      in
      CList.find_map_exn find_ind_ord m
    with Not_found -> cstr


  let reify env sigma m ty v : Constr.t = 
    let open Declarations in
    let debug s = debug Pp.(fun () -> str ("reify: ") ++ s ()) in
    let rec aux ty v =
    Control.check_for_interrupt ();
    let () = debug Pp.(fun () -> str "Reifying value of type " ++ pr_reifyable_value_type env sigma ty) in
    match ty with
    | IsInductive (hd, u, args) -> 
      let open Inductive in
      let open Inductiveops in
      let qhd = match Metarocq_template_plugin.Ast_quoter.quote_global_reference (IndRef hd) with Kernames.IndRef i -> i | _ -> assert false in
      let spec = lookup_mind_specif env hd in
      let npars = inductive_params spec in
      let params, _indices = CList.chop npars args in
      let indfam = make_ind_family ((hd, EConstr.EInstance.make u), List.map EConstr.of_constr params) in
      let cstrs = get_constructors env indfam in
      let cstrs = apply_reordering qhd m cstrs in
      if Obj.is_block v then
        let ord = Obj.tag v in
        let () = debug Pp.(fun () -> str (Printf.sprintf "Reifying constructor block of tag %i" ord)) in
        let coqidx = 
          try find_nth_non_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty
        in
        let cstr = cstrs.(coqidx) in
        let coqidx = find_reverse_mapping qhd m coqidx in
        let ctx = EConstr.Vars.smash_rel_context cstr.cs_args in
        let vargs = List.init (List.length ctx) (Obj.field v) in
        let args' = List.map2 (fun decl v -> 
          let argty = check_reifyable_value env sigma 
          (Context.Rel.Declaration.get_type decl) in
          aux argty v) (List.rev ctx) vargs in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) (params @ args')
      else (* Constant constructor *)
        let ord = (Obj.magic v : int) in
        let () = debug Pp.(fun () -> str @@ Printf.sprintf "Reifying constant constructor: %i" ord) in
        let coqidx = 
          try find_nth_constant ord cstrs 
          with Not_found -> ill_formed env sigma ty 
        in
        let coqidx = find_reverse_mapping qhd m coqidx in
        let () = debug Pp.(fun () -> str @@ Printf.sprintf "Reifying constant constructor: %i is %i in Rocq" ord coqidx) in
        Term.applistc (Constr.mkConstructU ((hd, coqidx + 1), u)) params
    | IsPrimitive (c, u, _args) -> 
      if Environ.is_array_type env c then 
        CErrors.user_err Pp.(str "Primitive arrays are not supported yet in MetaRocq r Extractioneification")
      else if Environ.is_float64_type env c then
        Constr.mkFloat (Obj.magic v)
      else if Environ.is_int63_type env c then
        Constr.mkInt (Obj.magic v)
      else CErrors.user_err Pp.(str "Unsupported primitive type in MetaRocq r Extractioneification")
    in aux ty v

  let reify opts env sigma tyinfo result =
    let mapping = opts.malfunction_pipeline_config.reorder_constructors in
    if opts.time then time opts (Pp.str "Reification") (reify env sigma mapping tyinfo) result
    else reify env sigma mapping tyinfo result

end


let loaded_modules = ref CString.Set.empty

type compilation_result = 
| SharedLib of string list * Reify.reifyable_type list * string
| StandaloneProgram of string

let compile opts names tyinfos fname = 
  match opts.program_type with
  | None -> None
  | Some t ->
    let malfunction = run_command opts (opam_command "which malfunction") in
    let ocamlfind = run_command opts (opam_command "which ocamlfind") in
    let packages = get_global_packages () in
    let optimize = if opts.optimize then "-O2" else "" in
    match t with
    | Plugin -> 
      let fname = 
        let basename = Filename.chop_extension fname in
        let freshname = next_string_away_from basename (fun s -> CString.Set.mem s !loaded_modules) in
        let freshfname = freshname ^ ".mlf" in
        if freshname <> basename then 
          ignore (execute opts (Printf.sprintf "mv %s %s" fname freshfname));
        loaded_modules := CString.Set.add freshname !loaded_modules;
        freshfname
      in
      let packages = "rocq_verified_extraction.plugin" :: packages in
      let compile_cmd = 
        Printf.sprintf "%s cmx %s -shared -package %s %s" malfunction optimize 
          (String.concat "," packages) fname
      in
      let _out, _err = execute opts compile_cmd in (* we now have fname . cmx *)
      let cmxfile =  Filename.chop_extension fname ^ ".cmx" in
      let cmxsfile = Filename.chop_extension fname ^ ".cmxs" in
      (* Build the shared library *)
      let link_cmd = 
        Printf.sprintf "%s opt -shared -package %s -o %s %s" ocamlfind 
         (String.concat "," packages) cmxsfile cmxfile
      in
      let _out, _err = execute opts link_cmd in
      Some (SharedLib (names, tyinfos, cmxsfile))
    | Standalone link_coq -> 
      let output = Filename.chop_extension fname in
      let flags, packages =
        if link_coq then 
          "-thread -linkpkg", String.concat "," (statically_linked_pkgs @ packages)
        else "-thread -linkpkg", String.concat "," packages
      in
      let compile_cmd = 
        Printf.sprintf "%s compile %s %s -package %s -o %s %s" 
          malfunction optimize flags packages output fname
      in
      let _out, _err = time opts Pp.(str "Compilation") (execute opts) compile_cmd in (* we now have fname . cmx *)
      notice opts Pp.(fun () -> str "Compiled to " ++ str output);
      Some (StandaloneProgram output)

let run_code opts env sigma tyinfo code : Constr.t =
  let open Reify in
  let value, tyinfo =
    match tyinfo with
    | IsThunk vty -> ((Obj.magic code : unit -> Obj.t) (), vty)
    | IsValue vty -> code, vty
  in
  Reify.reify opts env sigma tyinfo value

let run opts env sigma result : Constr.t list option =
  match result with
  | SharedLib (fns, tyinfos, shared_lib) ->
    if opts.load then begin
      time opts Pp.(str "Dynamically linking " ++ str shared_lib) Dynlink.loadfile_private shared_lib;
      if opts.run then begin
        debug Pp.(fun () -> str"Loaded shared library: " ++ str shared_lib);
        let run fn tyinfo = 
          match CString.Map.find_opt fn !register_plugins with
          | None -> CErrors.anomaly Pp.(str"Couldn't find funtion " ++ str fn ++ str" which should have been registered by " ++ str shared_lib)
          | Some code -> time opts Pp.(str fn) (run_code opts env sigma tyinfo) code
        in
        Some (List.map2 run fns tyinfos)
      end else None
    end else None

  | StandaloneProgram s -> 
    if opts.run then
      let out, err = time opts Pp.(str s) (execute opts) s in
      if err <> "" then Feedback.msg_warning (Pp.str err);
      if out <> "" then Feedback.msg_notice (Pp.str out);
      Some []
    else None

type malfunction_compilation_function =
  malfunction_pipeline_config -> malfunction_program_type -> TemplateProgram.template_program -> 
  string list * string

let decompose_argument env sigma c =
  let rec aux c =
    let fn, args = EConstr.decompose_app sigma c in
    match EConstr.kind sigma fn with
    | Construct (cstr, u) when Environ.QGlobRef.equal env (ConstructRef cstr) (Rocqlib.lib_ref "core.prod.intro") ->
      (match CArray.to_list args with
       | [ _; _; fst; snd ]
          -> aux fst @ [Reify.check_reifyable_thunk_or_value env sigma snd]
       |_ ->  [Reify.check_reifyable_thunk_or_value env sigma c])
    | _ -> [Reify.check_reifyable_thunk_or_value env sigma c]
  in aux c

let set_opam_env opts =
  let path = Unix.getenv "PATH" in
  let opam_binpath = 
    match Unix.getenv "OPAM_SWITCH_PREFIX" with
    | exception Not_found ->
      let opam_path = 
      match get_opam_path_opt () with
      | Some s -> s
      | None -> run_command opts "which opam"
      in
      run_command opts (opam_path ^ " var --safe bin")
    | pref -> pref ^ "/bin"
  in
  Unix.putenv "PATH" (opam_binpath ^ ":" ^ path)

let set_opam_env opts = if opts.use_opam_env then set_opam_env opts else ()

let extract_and_run
  (compile_malfunction : malfunction_compilation_function)
  ?loc opts env sigma c dest : (Constr.t list) option =
  let opts = make_options loc opts in
  let () = set_opam_env opts in 
  let prog = time opts Pp.(str"Quoting") (Ast_quoter.quote_term_rec ~bypass:opts.bypass_qeds env) sigma (EConstr.to_constr sigma c) in
  let pt = match opts.program_type with 
    | Some (Standalone _) | None -> Standalone_binary 
    | Some Plugin -> Shared_library ("Rocq_verified_extraction_plugin__Verified_extraction", "register_plugin")
  in
  let tyinfos =
    try decompose_argument env sigma c
    with e -> if not (opts.load || opts.run) then [] else raise e
  in
  let run_pipeline opts prog = compile_malfunction opts.malfunction_pipeline_config pt prog in
  let names, eprog = time opts Pp.(str"Extraction") (run_pipeline opts) prog in
  let names = if opts.load then 
      match tyinfos, names with
      | [_], [] -> ["main"]
      | _ ->
      if not (List.length names = List.length (tyinfos)) then
        CErrors.user_err ?loc Pp.(str "Extracted names " ++ prlist_with_sep spc str names ++ str " do not match argument types " ++ 
          prlist_with_sep spc (Reify.pr_reifyable_type env sigma) tyinfos)
      else names
    else names
  in
  let dest = 
    match dest with
    | Some _ -> dest
    | None -> if not (Option.is_empty opts.program_type) then Some "verified_extraction_term.mlf" else None
  in
  let dest = match dest with
  | None -> Feedback.msg_notice Pp.(str eprog); None
  | Some fname ->
    let fname = build_fname fname in
    let oc = open_out fname in (* Does not raise? *)
    let () = output_string oc eprog in
    let () = output_char oc '\n' in
    close_out oc;
    notice opts Pp.(fun () -> str"Extracted code written to " ++ str fname);
    Some fname
  in
  match dest with
  | None -> None
  | Some fname ->
    if opts.format then 
      let malfunction = run_command opts (opam_command "which malfunction") in
      let temp = fname ^ ".tmp" in
      ignore (execute opts (Printf.sprintf "%s fmt < %s > %s && mv %s %s" malfunction fname temp temp fname))
    else ();
    match compile opts names tyinfos fname with
    | None -> None
    | Some result -> run opts env sigma result
    
let print_results env sigma = function
  | None -> ()
  | Some [res] ->
    Feedback.msg_notice Pp.(str"  = " ++ Printer.pr_constr_env env sigma res)
  | Some res ->
    Feedback.msg_notice Pp.(str"  = (" ++ Pp.(prlist_with_sep (fun () -> str", ") (Printer.pr_constr_env env sigma) res) ++ str ")")

let eval_name (fn : string) =
  match CString.Map.find_opt fn !register_plugins with
  | None -> CErrors.anomaly Pp.(str"Couldn't find funtion " ++ str fn ++ str" in registered plugins")
  | Some code -> code

let eval_plugin_gen ?loc opts (gr : Libnames.qualid) =
  let opts = make_options loc opts in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let gr = globref_of_qualid gr in
  let c = match gr with Names.GlobRef.ConstRef c -> c | _ -> 
    CErrors.user_err Pp.(Printer.pr_global gr ++ str " does not bind to a reference") in
  let fn = Names.Constant.to_string c in
  let sigma, grc = Evd.fresh_global env sigma gr in
  let tyinfo = Reify.check_reifyable_thunk_or_value env sigma grc in
  let code = eval_name fn in
  let c = run_code opts env sigma tyinfo code in
  env, sigma, c

let eval_plugin ?loc opts (gr : Libnames.qualid) = 
  let env, sigma, c = eval_plugin_gen ?loc opts gr in
  print_results env sigma (Some [c])

let eval ?loc opts gr = 
  let env, sigma, c = eval_plugin_gen ?loc opts gr in
  c

let extract compile_malfunction ?loc opts env sigma c dest = 
  let res = extract_and_run compile_malfunction ?loc opts env sigma c dest in
  print_results env sigma res
