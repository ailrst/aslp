
open Asl_ast
open Asl_utils


module StringSet = Set.Make(String) ;;

type st = {
  mutable indent: int;
  mutable skip_seq: bool;
  oc : out_channel;
  mutable called_fun : StringSet.t;
  mutable output_fun: StringSet.t
}

let global_imports = ["util.Logger"]
let global_opens = ["ir"]

(**
and default_value t st =
  match t with
  | Type_Bits w -> Printf.sprintf "BitVecLiteral(0, %s)" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "TrueLiteral"
  | Type_Constructor (Ident "integer") -> "BigInt(0)"
  | Type_Constructor (Ident "rt_label") -> "0"
  | Type_Array(Index_Range(lo, hi),ty) ->
      let lo = prints_expr lo st in
      let hi = prints_expr hi st in
      let d = default_value ty st in
      Printf.sprintf "Range.Exclusive((%s), (%s)).map(%s).toList" lo hi d
  | _ -> failwith @@ "Unknown type for default value: " ^ (pp_type t)

Infer type
  *)

let infer_type e =
    let tint = Some (Type_Constructor (Ident "integer")) in
    let tbool  = Some (Type_Constructor (Ident "boolean"))  in
    let tbits = fun b -> Some (Type_Bits b) in
  match e with
  (* Boolean Expressions *)
  | Expr_Var(Ident "TRUE") -> tbool
  | Expr_Var(Ident "FALSE") -> tbool
  | Expr_TApply(FIdent("and_bool", 0), [], [a;b]) -> tbool
  | Expr_TApply(FIdent("or_bool", 0), [], [a;b]) -> tbool
  | Expr_TApply(FIdent("implies_bool", 0), [], [a;b]) -> tbool
  | Expr_TApply(FIdent("not_bool", 0), [], [a]) -> tbool

  (* Int Expressions using Z *)
  | Expr_LitInt i -> tint
  | Expr_TApply(FIdent("add_int", 0), [], [a;b]) -> tint
  | Expr_TApply(FIdent("sub_int", 0), [], [a;b]) -> tint
  | Expr_TApply(FIdent("mul_int", 0), [], [a;b]) -> tint
  | Expr_TApply(FIdent("frem_int", 0), [], [a;b]) -> tint

  (* Other operations *)
  | Expr_LitBits b -> tbits (Expr_LitInt (b))
  | Expr_Slices(e,[Slice_LoWd(i,w)]) -> tbits (w)
  | _ -> None


let prints_arg_type (t) : string =
  match t with
  | (Type_Bits _) -> "BitVecLiteral" 
  | (Type_Constructor (Ident "integer")) -> "BigInt"
  | (Type_Constructor (Ident "boolean")) -> "Boolean"
  | t -> failwith @@ "Unknown arg type: " ^ (pp_type t)

let prints_ret_type t =
  match t with
  | Some (Type_Constructor (Ident "boolean")) -> "Boolean"
  | None -> "Unit"
  | Some t -> failwith @@ "Unknown return type: " ^ (pp_type t)
(****************************************************************
 * String Utils
 ****************************************************************)

let inc_depth st = st.indent <- st.indent + 2
let dec_depth st = st.indent <- st.indent - 2

let funcall_to_sig (name: string) (targs: expr list) (args : expr list) = 
  let targs = List.mapi (fun i f -> (match (infer_type f) with 
    | Some(t) -> ("targ" ^ Int.to_string i ^ ": " ^ prints_arg_type t)
    | None -> ("targ" ^ (Int.to_string i) ^ ": " ^ pp_expr f)
  )) targs in
  let args = List.mapi (fun i f -> (match (infer_type f) with 
    | Some(t) -> ("arg" ^ Int.to_string i ^ ": " ^ prints_arg_type t)
    | None -> ("arg" ^ (Int.to_string i) ^ ": " ^ pp_expr f)
  )) args in
  name ^ "(" ^ (String.concat "," (targs@args)) ^ ")"

let replace s =
  String.fold_left (fun acc c ->
    if c = '.' then acc ^ "_"
    else if c = '#' then acc ^ "HASH"
    else acc ^ (String.make 1 c)) "" s


let plain_ident v : string =
  let s = (match v with
  | Ident n ->  n
  | FIdent (n,0) ->  n
  | FIdent (n,i) ->  n ^ "_" ^ (string_of_int i)) in
  replace s

let name_of_ident v : string =
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
      Printf.sprintf "((%s) && (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("or_bool", 0), [], [a;b]) ->
      Printf.sprintf "((%s) || (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("implies_bool", 0), [], [a;b]) ->
      Printf.sprintf "((!(%s)) || (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("not_bool", 0), [], [a]) ->
      Printf.sprintf " (!(%s))" (prints_expr a st)

  (* State Accesses *)
  | Expr_Var(v) -> (name_of_ident v)
  | Expr_Field(e, f) ->
      prints_expr e st ^ "." ^ name_of_ident f
  | Expr_Array(a,i) ->
      Printf.sprintf "(%s).get(%s)" (prints_expr a st) (prints_expr i st)

  (* Int Expressions using Z *)
  | Expr_LitInt i -> "BigInt(" ^ i ^ ")"
  | Expr_TApply(FIdent("add_int", 0), [], [a;b]) ->
      Printf.sprintf "((%s) + (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("sub_int", 0), [], [a;b]) ->
      Printf.sprintf "((%s) - (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("mul_int", 0), [], [a;b]) ->
      Printf.sprintf "((%s) * (%s))" (prints_expr a st) (prints_expr b st)
  | Expr_TApply(FIdent("frem_int", 0), [], [a;b]) ->
      let x  = (prints_expr a st) in let y = (prints_expr b st)  in
      Printf.sprintf "((%s) - ( (%s) * ((%s) / (%s))))"  x y x y 

  (* Other operations *)
  | Expr_LitBits b -> Printf.sprintf "BitVecLiteral(BigInt(\"%s\", 2), %d)" b (String.length b) 
  | Expr_Slices(e,[Slice_LoWd(i,w)]) ->
      let e = prints_expr e st in
      let i = prints_expr i st in
      let w = prints_expr w st in
      Printf.sprintf "bvextract((%s),(%s),(%s)), %s)" e i w w
  | Expr_TApply(f, targs, args) ->
      let f = name_of_ident f in
      print_endline (funcall_to_sig f targs args) ;
      let args = List.map (fun e -> prints_expr e st) (targs@args) in
      f ^ "(" ^ (String.concat ", " (args)) ^ ")"

  | Expr_LitString s -> "\"" ^ s ^ "\""
  | Expr_Tuple(es) -> "(" ^ (String.concat "," (List.map (fun e -> prints_expr e st) es)) ^ ")"
  | Expr_Unknown(ty) -> default_value ty st

  | _ -> failwith @@ "prints_expr: " ^ pp_expr e

and default_value t st =
  match t with
  | Type_Bits w -> Printf.sprintf "BitVecLiteral(0, %s)" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "TrueLiteral"
  | Type_Constructor (Ident "integer") -> "BigInt(0)"
  | Type_Constructor (Ident "rt_label") -> "0"
  | Type_Array(Index_Range(lo, hi),ty) ->
      let lo = prints_expr lo st in
      let hi = prints_expr hi st in
      let d = default_value ty st in
      Printf.sprintf "Range.Exclusive((%s), (%s)).map(%s).toList" lo hi d
  | _ -> failwith @@ "Unknown type for default value: " ^ (pp_type t)



(* End expr printing *)


let write_line s st =
  let padding = String.concat "" (List.init st.indent (fun _ -> " ")) in
  Printf.fprintf st.oc  "%s%s" padding s

let write_seq st =
  if st.skip_seq then
    st.skip_seq <- false
  else Printf.fprintf st.oc ";\n"

let write_nl st =
  Printf.fprintf st.oc "\n"

(****************************************************************
 * Prim Printing
 ****************************************************************)

let write_fun_return e st =
  let s = Printf.sprintf "(%s)" e in
  write_line s st

let write_proc_return st =
  write_line "()" st

let write_assert s st =
  let s = Printf.sprintf "assert (%s)" s in
  write_line s st

let write_unsupported st =
  write_line "throw Exception(\"not supported\")" st

let write_call f targs args st =
  let f = name_of_ident f in
  let args = targs @ args in
  let call = f ^ " (" ^ (String.concat ") (" args) ^ ")" in
  write_line call st

let write_ref v e st =
  let name = name_of_ident v in
  let s = Printf.sprintf "var %s = (%s) \n" name e in
  st.skip_seq <- true;
  write_line s st

let write_let v e st =
  let v = name_of_ident v in
  let s = Printf.sprintf "val %s = %s \n" v e in
  st.skip_seq <- true;
  write_line s st

let write_if_start c st =
  let s = Printf.sprintf "if (%s) then {\n" c in
  write_line s st

let write_if_elsif c st =
  write_nl st;
  let s = Printf.sprintf "} else if (%s) then {\n" c in
  write_line s st

let write_if_else st =
  write_nl st;
  write_line "} else {\n" st

let write_if_end st =
  write_nl st;
  write_line "}" st

(****************************************************************
 * Stmt Printing
 ****************************************************************)

let rec write_assign v e st =
  match v with
  | LExpr_Wildcard ->
      let s = Printf.sprintf "val _ = %s \n" e in
      st.skip_seq <- true;
      write_line s st

  | LExpr_Var v ->
      let v = name_of_ident v in
      let s = Printf.sprintf "%s = %s" v e in
      write_line s st

  | LExpr_Array (LExpr_Var v, i) ->
      let i = prints_expr i st in
      let v = name_of_ident v in
      let s = Printf.sprintf "%s = list_update (%s) (%s) (%s)" v v i e in
      write_line s st

  | LExpr_Field (l, f) ->
      let v = name_of_lexpr l in
      let s = Printf.sprintf "%s = %s" v e in
      write_line s st

  | LExpr_Tuple (ls) ->
      let vars = List.init (List.length ls) (fun i -> "tmp" ^ (string_of_int i)) in
      let v = "(" ^ String.concat "," vars ^ ")" in
      let s = Printf.sprintf "val %s = %s \n" v e in
      st.skip_seq <- true;
      write_line s st;
      List.iter2 (fun l e ->
        write_seq st;
        write_assign l e st
      ) ls vars

  | _ -> failwith @@ "write_assign: " ^ (pp_lexpr v)

let rec write_stmt s st =
  match s with
  | Stmt_VarDeclsNoInit(ty, vs, loc) ->
      let e = default_value ty st in
      List.iter (fun v -> write_ref v e st) vs

  | Stmt_VarDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      write_ref v e st

  | Stmt_ConstDecl(ty, v, e, loc) ->
      let e = prints_expr e st in
      write_let v e st

  | Stmt_Assign(l, r, loc) ->
      let e = prints_expr r st in
      write_assign l e st

  | Stmt_TCall(f, tes, es, loc) ->
      let tes = List.map (fun e -> prints_expr e st) tes in
      let es = List.map (fun e -> prints_expr e st) es in
      write_call f tes es st

  | Stmt_FunReturn(e, loc) ->
      write_fun_return (prints_expr e st) st

  | Stmt_ProcReturn(loc) ->
      write_proc_return st

  | Stmt_Assert(e, loc) ->
      write_assert (prints_expr e st) st

  | Stmt_Throw _ ->
      write_unsupported st

  | Stmt_If(c, t, els, f, loc) ->
      let rec iter = function
      | S_Elsif_Cond(c,b)::xs ->
          write_if_elsif (prints_expr c st) st;
          write_stmts b st;
          iter xs
      | [] -> () in
      write_if_start (prints_expr c st) st;
      write_stmts t st;
      iter els;
      if f <> [] then (write_if_else st; write_stmts f st);
      write_if_end st

  | _ -> failwith @@ "write_stmt: " ^ (pp_stmt s);

and write_stmts s st =
  inc_depth st;
  match s with
  | [] ->
      write_proc_return st;
      dec_depth st
  | x::xs ->
      write_stmt x st;
      List.iter (fun s ->
        write_seq st;
        write_stmt s st
      ) xs;
      dec_depth st;
      assert (not st.skip_seq)


let write_preamble imports opens st =
  Printf.fprintf st.oc "/* AUTO-GENERATED ASLp LIFTER FILE */\npackage aslloader\n";
  List.iter (fun n ->
    Printf.fprintf st.oc "import %s\n" n) imports;
  List.iter (fun n ->
    Printf.fprintf st.oc "import %s._\n" n) opens;
  Printf.fprintf st.oc "\n"


let write_epilogue (fid: AST.ident) st =
  Printf.fprintf st.oc "class %s {

  def decode(insn: BitVecLiteral) : Any = {
    %s(insn)
  }
}" (plain_ident fid) (name_of_ident fid)

open AST
module Bindings = Map.Make(AST.Id)

let init_st oc : st = { indent = 0; skip_seq=false;  oc ; called_fun=StringSet.empty; output_fun=StringSet.empty} 

let build_args (tys: ((ty * ident)  list)) targs args =
  let targs =  List.map (fun t -> name_of_ident t) targs in 
  let ta = List.map (fun (t, i) -> (name_of_ident i) ^ ": " ^ (prints_arg_type t)) tys in
  if List.length targs = 0 && List.length args = 0 then "()"
  else "(" ^ (String.concat "," (targs@ta)) ^ ")" 

let write_fn (name: AST.ident) (ret_tyo, argtypes, targs, args, _, body) st = 
  let args = build_args argtypes targs args in
  let ret = prints_ret_type ret_tyo in
  Printf.fprintf st.oc "def %s %s : %s = {\n" (name_of_ident name) args ret;
  write_stmts body st;
  Printf.fprintf st.oc "\n}\n"

(* Write an instruction file, containing just the behaviour of one instructions *)
let write_instr_file fn fnsig dir =
  let m = name_of_FIdent fn in
  let path = dir ^ "/" ^ m ^ ".scala" in
  let oc = open_out path in
  let st = init_st oc in
  write_preamble global_imports global_opens st;
  write_fn fn fnsig st;
  close_out oc;
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



