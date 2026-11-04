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

(* A line on what peregrine chose by itself, which -q hides *)
let note opts fmt =
  Printf.ksprintf (fun s -> if opts.verbose <> Quiet then prerr_endline ("peregrine: " ^ s)) fmt

let write_file f s =
  let c = open_out_bin f in
  output_string c s;
  close_out c

let copy src dst = write_file dst (read_file src)

(* [f] as an absolute path without . and .. *)
let absolute f =
  let f = if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  let parts = List.fold_left (fun acc p -> match p, acc with
      | ("" | "."), _ -> acc
      | "..", _ :: acc -> acc
      | "..", [] -> []
      | p, _ -> p :: acc) [] (String.split_on_char '/' f) in
  "/" ^ String.concat "/" (List.rev parts)

let rec remove f =
  if Sys.is_directory f then begin
    Array.iter (fun g -> remove (Filename.concat f g)) (Sys.readdir f);
    Sys.rmdir f
  end else Sys.remove f

(* A fresh directory, removed at exit unless --debug is given *)
let temp_dir opts =
  let d = Filename.temp_file "peregrine" "" in
  Sys.remove d;
  Sys.mkdir d 0o700;
  if opts.debug then prerr_endline ("peregrine: frontend files kept in " ^ d)
  else at_exit (fun () ->
    (* Holds only what peregrine and the frontends wrote: files and
       directories, no links *)
    try remove d with Sys_error _ -> ());
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

(* The nearest Rocq project file, from [dir] upwards *)
let rec rocq_project dir =
  match List.find_opt Sys.file_exists
          (List.map (Filename.concat dir) ["_RocqProject"; "_CoqProject"]) with
  | Some f -> Some f
  | None -> let parent = Filename.dirname dir in
    if parent = dir then None else rocq_project parent

(* The -Q, -R, -I and -arg options of a project file, with the paths made
   absolute by [path]. The file lists and other options are left out. *)
let project_args path f =
  let s = Str.global_replace (Str.regexp "#[^\n]*") "" (read_file f) in
  let words = Str.full_split (Str.regexp "\"[^\"]*\"\\|[^ \t\r\n]+") s
    |> List.filter_map (function
      | Str.Delim w -> Some (if w.[0] = '"' then String.sub w 1 (String.length w - 2) else w)
      | Str.Text _ -> None) in
  let rec args = function
    | ("-Q" | "-R") as o :: p :: n :: r -> o :: path p :: n :: args r
    | "-I" :: p :: r -> "-I" :: path p :: args r
    | "-arg" :: a :: r -> List.filter ((<>) "") (String.split_on_char ' ' a) @ args r
    | _ :: r -> args r
    | [] -> [] in
  args words

(* The logical path of the file [input] (absolute, ending in .v) in the
   load path [args], and the logical path of its directory *)
let logical_path args input =
  let rec bindings = function
    | ("-Q" | "-R") :: p :: n :: r -> (absolute p, n) :: bindings r
    | _ :: r -> bindings r
    | [] -> [] in
  let under (dir, _) =
    let dir = if dir = "/" then dir else dir ^ "/" in
    String.length input > String.length dir && String.sub input 0 (String.length dir) = dir in
  match List.sort (fun (a, _) (b, _) -> compare (String.length b) (String.length a))
          (List.filter under (bindings args)) with
  | [] -> None
  | (dir, name) :: _ ->
    let rel = String.sub input (String.length dir) (String.length input - String.length dir) in
    let rel = List.filter ((<>) "") (String.split_on_char '/' (Filename.chop_suffix rel ".v")) in
    let dirs = List.filter ((<>) "") (String.split_on_char '.' name) @ rel in
    let dirpath = String.concat "." (List.rev (List.tl (List.rev dirs))) in
    Some (String.concat "." dirs, dirpath)

(* Rocq: the entry is extracted with the Peregrine plugin. When the load path
   gives the input a logical path, a copy of the input that ends with the
   extraction is compiled under that logical path, so the names are those
   that Peregrine Extract gives inside the project. Otherwise a driver loads
   the input, and the names are those of a module named after the input. The load path comes from --frontend-arg or
   else from the nearest project file. *)
let rocq opts fo ~typed input d =
  let entry = entry "Rocq" fo in
  let input = absolute input in
  let user_paths = List.exists (fun a -> List.mem a ["-Q"; "-R"; "-I"]) fo.frontend_args in
  let args = match if user_paths then None else rocq_project (Filename.dirname input) with
    | None -> fo.frontend_args
    | Some f ->
      let dir = Filename.dirname f in
      note opts "automatically detected Rocq project file %s; using %s" f
        (String.concat " " (project_args Fun.id f));
      project_args (fun p -> if Filename.is_relative p then Filename.concat dir p else p) f
      @ fo.frontend_args in
  let base = Filename.basename (Filename.remove_extension input) in
  let str s = "\"" ^ subst "\"" "\"\"" s ^ "\"" in
  let loader = "From Peregrine.Plugin Require Import Loader.\n" in
  let extract = Printf.sprintf "Peregrine Extract%s %s %s.\n" (if typed then " Typed" else "") in
  let rocq args = run opts "rocq" ("compile" :: args)
    "install Rocq and the Peregrine plugin with `opam install rocq-peregrine`" in
  match if Filename.check_suffix input ".v" then logical_path args input else None with
  | Some (lp, dirpath) ->
    note opts "extracting from %s, the logical path of %s" lp input;
    (* A copy of the input, ending with the extraction, in a directory bound
       to the logical path of the input's directory. Requiring the compiled
       input instead fails when the project has a .vo of it too. *)
    let lib = Filename.concat d "lib" in
    Sys.mkdir lib 0o700;
    let copy = Filename.concat lib (Filename.basename input) in
    let out = Filename.concat d "out.ast" in
    write_file copy (read_file input ^ "\n" ^ loader ^ extract (str out) entry);
    rocq (args @ ["-Q"; lib; dirpath; "-noglob"; copy]);
    out, []
  | None ->
    let base = if Str.string_match (Str.regexp "[A-Za-z_][A-Za-z0-9_']*$") base 0 then base else "Input" in
    note opts "%s is in no load path: loading it into a module named %s" input base;
    let driver = Filename.concat d (base ^ ".v") in
    let out = Filename.concat d (base ^ ".ast") in
    (* Load reads only files ending in .v *)
    let source =
      if Filename.check_suffix input ".v" then input
      else let c = Filename.concat d (base ^ "_source.v") in copy input c; c in
    write_file driver ("Load " ^ str source ^ ".\n" ^ loader ^ extract (str out) entry);
    rocq (args @ [driver]);
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
    | Some r -> note opts "automatically detected Lake project %s" r; r
    | None -> fail unsupported "%s is in no Lake project: the Lean frontend needs one that requires LeanToLambdaBox (https://github.com/peregrine-project/lean-to-lambdabox)" input in
  let copy = Filename.concat d (Filename.basename input) in
  let out = Filename.concat d "out.ast" in
  let str s = "\"" ^ subst "[\\\"]" "\\\\\\0" s ^ "\"" in
  let config = match fo.lean_config with Some c -> " config " ^ c | None -> "" in
  write_file copy (Printf.sprintf "import LeanToLambdaBox\n%s\n#erase %s%s to %s\n"
    (read_file input) entry config (str out));
  run opts ~cwd:root "lake" (["env"; "lean"] @ fo.frontend_args @ [copy])
    "install Lean with elan, https://lean-lang.org/install/";
  note opts "automatically passing the inlinings that #erase wrote as attributes";
  out, [out ^ ".inlinings"]

(* The lambda box program of [input], with the attribute files that its
   frontend wrote and the path to name the outputs after: [input] without its
   extension. [typed] asks the frontend for typed lambda box, if it has it. *)
let load opts fo ~typed input =
  let fe, stem = infer input in
  if fo.from = None && fe <> LambdaBox then
    note opts "automatically detected: %s is %s source, from its extension" input
      (match fe with Rocq -> "a Rocq" | Agda -> "an Agda" | _ -> "a Lean");
  let fe = Option.value fo.from ~default:fe in
  if fo.lean_config <> None && fe <> Lean then
    fail unsupported "--lean-config applies only to a Lean source";
  if fe <> LambdaBox && not fo.typed then
    if typed then note opts "automatically asking for typed lambda box, which the backend needs%s"
        (if fe = Lean then " (Lean has none: the types will be inferred)" else "")
    else note opts "automatically asking for untyped lambda box (--typed asks for typed)";
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
