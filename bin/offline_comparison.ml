open LibASL
open Testing
open Asl_ast
open Asl_visitor
open Value


let fr = "results.marshall"

let env = Option.get (Eval.aarch64_evaluation_environment ~verbose:false ())

let dis_online (iset: string) (op: int): stmt list opresult =
  let lenv = Dis.build_env env in
  let decoder = Eval.Env.getDecoder env (Ident iset) in
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) (Z.of_int op) in
  try
    let stmts = Dis.dis_decode_entry env lenv decoder (VBits bv) in
    Result.Ok stmts
  with
    | e -> Result.Error (Op_DisFail e)


let dis_offline (op: int): stmt list opresult =
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) (Z.of_int op) in
  try
    let stmts = OfflineASL.Offline.run bv in
    Result.Ok stmts
  with
    | e -> Result.Error (Op_DisFail e)

let unres r = match r with 
  | Result.Ok stmts -> stmts
  | Result.Error _ -> []
    
module StringMap = Map.Make(String) 

type res = {
  online: stmt list ;
  offline: stmt list ;
}

type resultstype = (bitsLit * (i * (stmt list * stmt list)) list) list

let count_stmts_list (s:stmt list) : int = 
  let v = (new Scala_backend.stmt_counter) in
  visit_stmts v s |> ignore ;
  (v#gexpr_count + v#gstmt_count)
  
  

let loadr ()  = 
  Printf.printf "Loading marhsalled\n";
  let ic = open_in fr in
  let res :resultstype  = Marshal.from_channel ic in
  StringMap.of_list res


let op_test_opcode (env: Env.t) (iset: string) (op: int) =
  let disstmts = dis_online iset op in
  let disstmts_off =  dis_offline op in
  {online=unres disstmts; offline=unres disstmts_off}

let run opt_verbose instr env: resultstype  =
  Printf.printf "decodeall %s\n" instr;
  let iset = "A64" in
  let encodings = get_opcodes opt_verbose iset instr env in
  let ((results) : (bitsLit * (i * (stmt list * stmt list)) list) list)  = List.concat_map (fun (enc, fields, opt_opcodes) ->
      Printf.printf "\nENCODING: %s\n" enc;
      match opt_opcodes with
      | None -> Printf.printf "(encoding unused)\n"; []
      | Some opcodes ->
          let decodings = List.concat_map (fun (op, valid) ->
              if valid then
                let a, b = (hex_of_int op), op_test_opcode env iset op  in
                (*let printssl sl = String.concat "\n" (List.map (fun s -> Utils.to_string (Asl_parser_pp.pp_stmt s)) sl) in 
                print_endline (printssl (unres b.online))  ;
                print_endline (printssl  (unres b.offline))  ; *)
                flush stdout;
                [op, (b.online,b.offline)]
              else []
      ) opcodes in
        [enc, decodings]
  ) encodings in
  (results)


let rec process_command tcenv env cmd =
  match String.split_on_char ' ' cmd with
  | (":set" :: "impdef" :: rest) ->
        let cmd = String.concat " " rest in
        let (x, e) = LoadASL.read_impdef tcenv Unknown cmd in
        let v = Eval.eval_expr Unknown env e in
        Eval.Env.setImpdef env x v
  | [":project"; prj] ->
      let inchan = open_in prj in
      (try
          while true do
              process_command tcenv env (input_line inchan)
          done
      with
      | End_of_file ->
          close_in inchan
      )
  | [""] -> ()
  | _ -> Printf.printf "Ignoring: %s\n" cmd


let do_lift () = 
  let opt_verbose = ref true in
  let env = match Eval.aarch64_evaluation_environment ~verbose:!opt_verbose () with
  | Some e -> e
  | _ -> failwith "Unable to build evaluation environment." in
  let patterns = [
    "aarch64_integer.+";
    "aarch64_branch.+";
    "aarch64_float_.+";
    "aarch64_vector_arithmetic_binary.+";
    "aarch64_vector_(?!arithmetic_binary).+";
    "aarch64_memory_.+"
  ]
  in
  let filenames = Option.get Eval.aarch64_asl_files in
  let prj_files = List.filter (fun f -> Utils.endswith f ".prj") (snd filenames) in
  let tcenv = Tcheck.Env.mkEnv Tcheck.env0 in
  List.iter (fun f -> process_command tcenv env (":project " ^ f)) prj_files;
  let ress : resultstype = (List.concat_map (fun instr -> run opt_verbose instr env) patterns) in
  let oc = open_out fr in
  Marshal.to_channel oc ress [];
  close_out oc;
  StringMap.of_list ress


let group_list (k: 'b -> 'a) (l: 'b list) : ('a * 'b list) list   = 
  let keys : 'a list = List.map (k) l in
  let grouped = List.map (fun key -> (key, List.find_all (fun e -> (k e) = key) l)) keys in
  grouped

let main () = 
  let ress  = if (Sys.file_exists fr) then loadr () else do_lift () in
  let sum = List.fold_left (+) 0 in
  let mmax = List.fold_left (max) 0 in

  let stmtcounts = open_out ("stmt-counts.csv") in

  output_string stmtcounts "decode,maxonline,maxoffline\n" ;

  StringMap.iter (fun k (v : (i * (stmt list * stmt list)) list)  -> 
    let counts = List.map (fun (op, (online, offline)) -> (count_stmts_list online), (count_stmts_list offline)) v  in
    let counts_on = mmax (List.map fst counts) in
    let counts_off = mmax (List.map snd counts) in
    let s = Printf.sprintf "%s,%d,%d\n" k counts_on counts_off in
    output_string stmtcounts s ;
    Printf.printf "%s" s ;

    let op, (online, offline) = (List.find (fun (op, (online, offline)) -> (counts_on) = (count_stmts_list online)) v) in
    (* diffs *)
      let name = Printf.sprintf "comparout/%s-%x-" k op in
      let printssl sl = String.concat "\n" (List.map (fun s -> Utils.to_string (Asl_parser_pp.pp_stmt s)) sl) in 
      let offlinechan = open_out (name ^ "offline") in
      let onlinechan = open_out (name ^ "online") in
      output_string offlinechan (printssl offline) ;
      output_string onlinechan (printssl online) ;
      close_out offlinechan; 
      close_out onlinechan;
  ) ress;
  close_out stmtcounts;
  ress 



let () = main () |> ignore
