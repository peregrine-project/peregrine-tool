(* Running the proof-assistant frontends, which turn a source file into a
   lambda box program. Each frontend is an external tool, run in a temporary
   directory. *)
open Common

let names = ["rocq", Rocq; "agda", Agda; "lean", Lean; "lambdabox", LambdaBox]

(* The literate Agda extensions are those of Agda 2.8 *)
let extensions = [
  ".v", Rocq;
  ".agda", Agda; ".lagda", Agda; ".lagda.tex", Agda; ".lagda.rst", Agda;
  ".lagda.md", Agda; ".lagda.org", Agda; ".lagda.tree", Agda; ".lagda.typ", Agda;
  ".lean", Lean;
]

(* The frontend of [f], from its extension, and [f] without that extension *)
let infer f =
  match List.find_opt (fun (e, _) -> Filename.check_suffix f e) extensions with
  | Some (e, fe) -> fe, Filename.chop_suffix f e
  | None -> LambdaBox, Filename.remove_extension f

(* Exit codes 30 to 39, see [exits] in main.ml *)
let tool_missing = 30
let tool_failed = 31
let unsupported = 32

let fail code fmt =
  Printf.ksprintf (fun s -> prerr_endline ("peregrine: " ^ s); exit code) fmt

let write_file f s =
  let c = open_out_bin f in
  output_string c s;
  close_out c

let copy src dst = write_file dst (read_file src)

let absolute f =
  if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f

(* A fresh directory, removed at exit unless --debug is given *)
let temp_dir opts =
  let d = Filename.temp_file "peregrine" "" in
  Sys.remove d;
  Sys.mkdir d 0o700;
  if opts.debug then prerr_endline ("peregrine: frontend files kept in " ^ d)
  else at_exit (fun () ->
    (* The frontends write files only, no subdirectories *)
    Array.iter (fun f -> try Sys.remove (Filename.concat d f) with Sys_error _ -> ())
      (try Sys.readdir d with Sys_error _ -> [||]);
    try Sys.rmdir d with Sys_error _ -> ());
  d

let run opts ?cwd tool args install =
  let cmd = Filename.quote_command tool args in
  let cmd = match cwd with
    | Some d -> "cd " ^ Filename.quote d ^ " && " ^ cmd
    | None -> cmd in
  if opts.verbose = Verbose then prerr_endline cmd;
  match Sys.command cmd with
  | 0 -> ()
  | 127 -> fail tool_missing "%s not found on the PATH; %s" tool install
  | n -> fail tool_failed "%s failed with exit code %d" tool n

let entry name fo =
  match fo.entry with
  | Some e -> e
  | None -> fail unsupported "a %s input needs --entry NAME, the definition to extract" name

let subst re by s = Str.global_replace (Str.regexp re) by s

(* Rocq: a driver file loads the input and extracts the entry with the
   Peregrine plugin. The driver has the name of the input, so that the
   extracted names are those of a module of that name. *)
let rocq opts fo ~typed input d =
  let entry = entry "Rocq" fo in
  let base = Filename.basename (Filename.remove_extension input) in
  let base = if Str.string_match (Str.regexp "[A-Za-z_][A-Za-z0-9_']*$") base 0 then base else "Input" in
  let driver = Filename.concat d (base ^ ".v") in
  let out = Filename.concat d (base ^ ".ast") in
  let str s = "\"" ^ subst "\"" "\"\"" s ^ "\"" in
  (* Load reads only files ending in .v *)
  let source =
    if Filename.check_suffix input ".v" then absolute input
    else let c = Filename.concat d (base ^ "_source.v") in copy input c; c in
  write_file driver (Printf.sprintf
    "Load %s.\nFrom Peregrine.Plugin Require Import Loader.\nPeregrine Extract%s %s %s.\n"
    (str source) (if typed then " Typed" else "") (str out) entry);
  run opts "rocq" ("compile" :: fo.frontend_args @ [driver])
    "install Rocq and the Peregrine plugin with `opam install rocq-peregrine`";
  out, []

(* Agda: agda2lambox extracts the definitions marked with a COMPILE
   AGDA2LAMBOX pragma, the first of them as the main term. It runs in the
   directory of the input, which is the project root of a module without a
   header. *)
let agda opts fo ~typed input d =
  if fo.entry <> None then
    fail unsupported "agda2lambox has no option to select a definition: mark it with {-# COMPILE AGDA2LAMBOX NAME #-} in the source instead of passing --entry";
  let input = absolute input in
  run opts ~cwd:(Filename.dirname input) "agda2lambox"
    ((if typed then ["--typed"] else []) @ ["-o"; d] @ fo.frontend_args @ [input])
    "build it from https://github.com/agda/agda2lambox";
  match List.filter (fun f -> Filename.check_suffix f ".ast") (Array.to_list (Sys.readdir d)) with
  | [f] -> Filename.concat d f, []
  | _ -> fail tool_failed "agda2lambox wrote no lambda box program"

let rec lake_root dir =
  if List.exists (fun f -> Sys.file_exists (Filename.concat dir f)) ["lakefile.lean"; "lakefile.toml"]
  then Some dir
  else let parent = Filename.dirname dir in
    if parent = dir then None else lake_root parent

(* Lean: a copy of the input that imports LeanToLambdaBox and ends with
   #erase, checked by `lake env lean` in the nearest Lake project. #erase
   writes, next to the program, the attribute file of the constants to
   inline. *)
let lean opts fo ~typed:_ input d =
  if fo.typed then fail unsupported "the Lean frontend has no typed output";
  let entry = entry "Lean" fo in
  let input = absolute input in
  let root = match lake_root (Filename.dirname input) with
    | Some r -> r
    | None -> fail unsupported "%s is in no Lake project: the Lean frontend needs one that requires LeanToLambdaBox (https://github.com/peregrine-project/lean-to-lambdabox)" input in
  let copy = Filename.concat d (Filename.basename input) in
  let out = Filename.concat d "out.ast" in
  let str s = "\"" ^ subst "[\\\"]" "\\\\\\0" s ^ "\"" in
  write_file copy (Printf.sprintf "import LeanToLambdaBox\n%s\n#erase %s to %s\n"
    (read_file input) entry (str out));
  run opts ~cwd:root "lake" (["env"; "lean"] @ fo.frontend_args @ [copy])
    "install Lean with elan, https://lean-lang.org/install/";
  out, [out ^ ".inlinings"]

(* The lambda box program of [input], with the attribute files that its
   frontend wrote and the path to name the outputs after: [input] without its
   extension. [typed] asks the frontend for typed lambda box, if it has it. *)
let load opts fo ~typed input =
  let fe, stem = infer input in
  let fe = Option.value fo.from ~default:fe in
  let typed = typed || fo.typed in
  let ast, attrs = match fe with
    | LambdaBox ->
      if fo.entry <> None || fo.typed || fo.frontend_args <> [] then
        fail unsupported "--entry, --typed and --frontend-arg apply to a proof-assistant source, not to a lambda box program";
      input, []
    | Rocq -> rocq opts fo ~typed input (temp_dir opts)
    | Agda -> agda opts fo ~typed input (temp_dir opts)
    | Lean -> lean opts fo ~typed input (temp_dir opts) in
  (match fo.keep_ast with
   | Some p when fe <> LambdaBox ->
     copy ast p;
     List.iter (fun a -> copy a (p ^ Filename.extension a)) attrs
   | _ -> ());
  ast, attrs, stem
