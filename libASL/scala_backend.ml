
open Asl_ast
open Asl_utils


type st = {
  mutable indent: int;
  oc : out_channel
}

let global_imports = ["util.Logger"]
let global_opens = ["ir"]

(****************************************************************
 * String Utils
 ****************************************************************)

let replace s =
  String.fold_left (fun acc c ->
    if c = '.' then acc ^ "_"
    else if c = '#' then acc ^ "HASH"
    else acc ^ (String.make 1 c)) "" s

let name_of_ident v =
  let s = (match v with
  | Ident n -> "v_" ^ n
  | FIdent (n,0) -> "f_" ^ n
  | FIdent (n,i) -> "f_" ^ n ^ "_" ^ (string_of_int i)) in
  replace s

let rec name_of_lexpr l =
  match l with
  | LExpr_Var v -> name_of_ident v
  | LExpr_Field (l, f) ->
      let l = name_of_lexpr l in
      let f = name_of_ident f in
      l ^ "." ^ f
  | LExpr_Wildcard -> "_"
  | _ -> failwith @@ "name_of_lexpr: " ^ (pp_lexpr l)

(* Expr printing *)


let rec prints_expr e st =
  match e with
  (* Boolean Expressions *)
  | Expr_Var(Ident "TRUE") -> "TrueLiteral"
  | Expr_Var(Ident "FALSE") -> "FalseLiteral"
  | Expr_TApply(FIdent("and_bool", 0), [], [a;b]) ->
      Printf.sprintf "BinaryExpr(BoolAND, (%s), (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("or_bool", 0), [], [a;b]) ->
      Printf.sprintf "BinaryExpr(BoolOR, (%s), (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("implies_bool", 0), [], [a;b]) ->
      Printf.sprintf "BinaryExpr(BoolIMPLIES, (%s), (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("not_bool", 0), [], [a]) ->
      Printf.sprintf "UnaryExpr(BoolNOT, (%s))" (prints_expr a st)

  (* State Accesses *)
  | Expr_Var(v) -> Printf.sprintf("LocalVar(\"%s\", BitVecType(-1))") (name_of_ident v)
  | Expr_Field(e, f) ->
      prints_expr e st ^ "." ^ name_of_ident f
  | Expr_Array(a,i) ->
      Printf.sprintf "(%s).get(%s)" (prints_expr a st) (prints_expr i st)

  (* Int Expressions using Z *)
  | Expr_LitInt i -> "BigInt(" ^ i ^ ")"
  | Expr_TApply(FIdent("add_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) + (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("sub_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) - (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("mul_int", 0), [], [a;b]) ->
      Printf.sprintf "(%s) * (%s)" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("frem_int", 0), [], [a;b]) ->
      let x  = (prints_expr a st) in let y = (prints_expr b st)  in
      Printf.sprintf "(%s) - ( (%s) * ((%s) / (%s)) ) "  x y x y 

  (* Other operations *)
  | Expr_LitBits b -> "from_bitsLit (\"" ^ b ^ "\")"
  | Expr_Slices(e,[Slice_LoWd(i,w)]) ->
      let e = prints_expr e st in
      let i = prints_expr i st in
      let w = prints_expr w st in
      Printf.sprintf "extract_bits((%s),(%s),(%s))" e i w
  | Expr_TApply(f, targs, args) ->
      let f = name_of_ident f in
      let args = List.map (fun e -> prints_expr e st) (targs @ args) in
      f ^ " (" ^ (String.concat ") (" args) ^ ")"

  | Expr_LitString s -> "\"" ^ s ^ "\""
  | Expr_Tuple(es) -> "(" ^ (String.concat "," (List.map (fun e -> prints_expr e st) es)) ^ ")"
  | Expr_Unknown(ty) -> default_value ty st

  | _ -> failwith @@ "prints_expr: " ^ pp_expr e

and default_value t st =
  match t with
  | Type_Bits w ->
      Printf.sprintf "mkBits (%s) Z.zero" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "true"
  | Type_Constructor (Ident "integer") -> "Z.zero"
  | Type_Constructor (Ident "rt_label") -> "0"
  | Type_Array(Index_Range(lo, hi),ty) ->
      let lo = prints_expr lo st in
      let hi = prints_expr hi st in
      let d = default_value ty st in
      Printf.sprintf "List.init ((Z.to_int (%s)) - (Z.to_int (%s)) + 1) (fun _ -> %s)" hi lo d
  | _ -> failwith @@ "Unknown type for default value: " ^ (pp_type t)

let prints_ret_type t =
  match t with
  | Some (Type_Constructor (Ident "boolean")) -> "bool"
  | None -> "unit"
  | Some t -> failwith @@ "Unknown return type: " ^ (pp_type t)

(* End expr printing *)

let write_preamble imports opens st =
  Printf.fprintf st.oc "/* AUTO-GENERATED ASLp LIFTER FILE */";
  List.iter (fun n ->
    Printf.fprintf st.oc "import %s\n" n) imports;
  List.iter (fun n ->
    Printf.fprintf st.oc "import %s._\n" n) opens;
  Printf.fprintf st.oc "\n"

let write_epilogue (fid: AST.ident) st =
  Printf.fprintf st.oc "def run(inp: int) =\n  reset_ir ();\n  %s enc;\n  get_ir ()\n" (name_of_ident fid)

open AST
module Bindings = Map.Make(AST.Id)


let init_st oc : st = { indent = 0;  oc } 

let write_fn (name: AST.ident ) (ret_tyo,_,targs,args,_,body) st = ()



(* Write an instruction file, containing just the behaviour of one instructions *)
let write_instr_file fn fnsig dir =
  name_of_FIdent fn 

(* Write the decoder file - should depend on all of the above *)
let write_decoder_file fn fnsig deps dir =
  let m = "aslpOffline" in
  let path = dir ^ "/" ^ m ^ ".scala" in
  let oc = open_out path in
  let st = init_st oc in
  write_preamble global_imports (global_opens @ deps) st;
  write_fn fn fnsig st;
  write_epilogue fn st;
  close_out oc;
  m 

(* Write all of the above, expecting Utils.ml to already be present in dir *)
(* decoder fun decodef fnsig, test funs, instruction funs, output directory  

   (ast_utils functions for accessing parts of function signature tuple)

  let files = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig dir)::acc) fns [] in
  write_decoder_file dfn dfnsig files dir |> ignore
   *)
let run (dfn: AST.ident) dfnsig tests fns dir : unit =
  let files = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig dir)::acc) fns [] in
  write_decoder_file dfn dfnsig files dir |> ignore ; 
  ()



