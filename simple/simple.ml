
(****************************************************************
 *  Simple cacheable interface to ASLp 
 *  
 *   - provides retrievbeDisassemblyu while locating the appropriate 
 *     prelude and enviornment  
 *
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

open LibASL
open List
open LibASL.Resources

let prelude_text: string = prelude_dot_asl

let () = Random.init 4

let new_id _ : bytes = (Bytes.create 8) |> Bytes.map (fun _ -> Char.chr (Random.int 256)) 


type retrieve_env = 
  {
    decls: Asl_ast.declaration list;
    eval_env: Eval.Env.t;
    id: bytes;
  }
;; 

let default_environment_cached: retrieve_env option ref = ref None

let default_environment _ : retrieve_env = 
  match !default_environment_cached with 
    | Some(x) -> x 
    | None -> (let decls: Asl_ast.declaration list =
      (let prelude = LoadASL.read_text prelude_text "prelude.asl" true false     in
      let mra     = map (fun t -> LoadASL.read_text t "" false false) asl_defs_text in
      concat (prelude :: mra)) in
    let persistent_env = Eval.build_evaluation_environment decls in
    let res = {
      decls= decls;
      eval_env= persistent_env;
      id = new_id ();
    } in
    default_environment_cached := Some(res); 
    res)

let from_file_environment (prelude: string) (filenames: string list): retrieve_env = 
        let t  = LoadASL.read_file prelude true false in
        let ts = List.map (fun filename ->
                if Utils.endswith filename ".spec" then begin
                    LoadASL.read_spec filename false
                end else if Utils.endswith filename ".asl" then begin
                    LoadASL.read_file filename false false
                end else if Utils.endswith filename ".prj" then begin
                    [] (* ignore project files here and process later *)
                end else begin
                    failwith ("Unrecognized file suffix on "^filename)
                end
                ) filenames 
        in
    let decls = concat (t :: ts) in
  let persistent_env = Eval.build_evaluation_environment decls in
  let res = {
    decls= decls;
    eval_env= persistent_env;
    id = new_id ();
  } in
  res

let environment (prelude_filename: string option) (other_filenames: string list) = 
  match (prelude_filename, other_filenames) with 
  | None, [] -> (default_environment ())
  | (Some prelude), (fnames) -> (from_file_environment prelude fnames)
  | (None) , _ -> failwith ("Must specify prelude") 

let eval_instr (opcode: string) ?(env=(default_environment ())) : string = 
    let praw a = Utils.to_string (Asl_parser_pp.pp_raw_stmt a) |> String.trim  in
    let address = None  in
    let res     = Dis.retrieveDisassembly ?address (env.eval_env) (Dis.build_env env.eval_env) opcode in 
    let ascii   = map praw res                                                 in
    let indiv s = init (String.length s) (String.get s) |> map (String.make 1)  in
    map indiv ascii |>  map (String.concat "") |> String.concat "\n"

let _ = Callback.register "aslpoop" eval_instr
