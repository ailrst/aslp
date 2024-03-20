
open Asl_ast
open Asl_utils


module StringTbl = Hashtbl.Make(String) ;;
module IntTbl = Map.Make(Int) ;;
module DefSet = Set.Make(struct 
  type t = (ident * ty) 
  let compare (a,b) (c,d) = (match (Stdlib.compare a c) with
      | 0 -> Stdlib.compare b d 
      | s -> s)
end)


let (let@) x f = fun s ->
  let (s,r) = x s in
  (f r) s
let (let+) x f = fun s ->
  let (s,r) = x s in
  (s,f r)


module LocMap = Map.Make(struct
  type t = l
  let compare = Stdlib.compare
end)

class find_defs = object (self)
  inherit Asl_visitor.nopAslVisitor
  val mutable defs = LocMap.empty 

  method add_dep loc i = defs <- LocMap.add loc i defs 
  method get_deps = defs

  method! vstmt = function
    | Stmt_VarDeclsNoInit(ty, [v], loc) -> self#add_dep loc (v, ty); SkipChildren
    | Stmt_VarDecl(ty, v, e, loc) -> self#add_dep loc (v ,ty); SkipChildren
    | Stmt_ConstDecl(ty, v, e, loc) -> self#add_dep loc (v , ty) ; SkipChildren
    | _ -> DoChildren
end 

let definedat body =  
  let v = new find_defs in
  Asl_visitor.visit_stmts v body |> ignore ;
  v#get_deps


type fsig = {
  name: string;
  targs: (ty option) list;
  args: (ty option) list;
}

type st = {
  mutable indent: int;
  mutable skip_seq: bool;
  oc : out_channel;
  (* Function calls detected *)
  mutable called_fun : fsig StringTbl.t;
  (* Function implementations generated *)
  mutable output_fun: fsig StringTbl.t;
  (* mapping indent level -> scope count *) 
  mutable decl_scopes: int IntTbl.t;

  mutable definitions : DefSet.t;
}

let global_imports = ["util.Logger"]
let global_opens = ["ir"]

let uniq_counter : int ref = ref 0 

let new_index _ : int = uniq_counter := !uniq_counter + 1 ; !uniq_counter

let get_decl_scope st = 
  ((IntTbl.find_opt  st.indent st.decl_scopes) |> (function 
    | Some(t) -> t
    | None -> 0)) 



let add_decl_scope st = 
   st.decl_scopes <- (IntTbl.add st.indent ((get_decl_scope st) + 1) st.decl_scopes)

let clear_decl_scope st = 
   st.decl_scopes <- (IntTbl.add st.indent (0) st.decl_scopes)


let mergeSig (a: fsig) (b: fsig) : fsig = 
  let merge x y = List.map2 (fun a b -> (match (a, b) with
    | (Some x, _) -> Some x
    | (_, Some x) -> Some x
    | _ -> None
  )) x y in
  {name = a.name; targs = (merge a.targs b.targs); args = (merge a.args b .args)}
  

(* Shallow inspection of an expression to guess its type. *)
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
  | Type_Constructor (Ident "rt_label") -> "Expr"
  | Type_Constructor (Ident "rt_sym") -> "Expr"
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

let funcall_to_sig (name: string) (targs: expr list) (args : expr list) : fsig = 
  let targs = List.map infer_type targs in
  let args = List.map infer_type args in
  {name=name; targs=targs; args=args}

let update_funcalls (f:fsig) (tbl: fsig StringTbl.t) : unit = 
  match (StringTbl.find_opt (tbl) f.name) with 
    | Some e -> StringTbl.replace tbl f.name (mergeSig e f)
    | None -> StringTbl.add (tbl) f.name f

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
  | Expr_Var(Ident "TRUE") -> "true"
  | Expr_Var(Ident "FALSE") -> "false"
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
      Printf.sprintf "bvextract(%s,%s,%s, %s)" e i w w
  | Expr_TApply(f, targs, args) ->
      let f = name_of_ident f in
      update_funcalls (funcall_to_sig f targs args) st.called_fun  ; 
      let args = List.map (fun e -> prints_expr e st) (targs@args) in
      f ^ "(" ^ (String.concat ", " (args)) ^ ")"

  | Expr_LitString s -> "\"" ^ s ^ "\""
  | Expr_Tuple(es) -> "(" ^ (String.concat "," (List.map (fun e -> prints_expr e st) es)) ^ ")"
  | Expr_Unknown(ty) -> default_value ty st (* Sound? *)

  | _ -> failwith @@ "prints_expr: " ^ pp_expr e

and default_value t st =
  match t with
  | Type_Bits w -> Printf.sprintf "BitVecLiteral(0, %s)" (prints_expr w st)
  | Type_Constructor (Ident "boolean") -> "true"
  | Type_Constructor (Ident "integer") -> "BigInt(0)"
  | Type_Constructor (Ident "rt_label") -> "null"
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
  else Printf.fprintf st.oc "\n"

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

let write_call f (targs : typeid list) (args: typeid list) st =
  let f = name_of_ident f in
  let args = targs @ args in
  let call = f ^ " (" ^ (String.concat "," args) ^ ")" in
  write_line call st

let write_ref v ty e st =
  let name = name_of_ident v in
  let s = Printf.sprintf "var %s : %s = (%s) \n" name (prints_arg_type ty) e in
  st.skip_seq <- true;
  write_line s st

let write_let v ty e st =
  let v = name_of_ident v in
  let s = Printf.sprintf "val %s : %s = %s \n" v (prints_arg_type ty) e in
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
      let vars = List.init (List.length ls) (fun i -> "tmp" ^ (string_of_int (new_index ()))) in
      let v = "(" ^ String.concat "," vars ^ ")" in
      let s = Printf.sprintf "val %s = %s \n" v e in
      st.skip_seq <- true;
      write_line s st;
      List.iter2 (fun l e ->
        write_seq st;
        write_assign l e st
      ) ls vars

  | _ -> failwith @@ "write_assign: " ^ (pp_lexpr v)


(*let add_def d t defs =  DefSet.add (d, t) defs *)

type block = { 
  mutable stmts: stmt list;
  mutable defs: DefSet.t;
}

type proc = {
  name: ident;
  mutable params: DefSet.t;
  mutable blocks: block list;
}


type funwork = {
  mutable procs: proc list;
  mutable bl: block;
  mutable pr: proc;
}

let init_fn name params: funwork = {procs = []; bl = {stmts = []; defs = params} ; pr = {name=name; params=params; blocks = []}}

let empty_block _ = {stmts=[]; defs = DefSet.empty}
let continue_block b = {b with stmts=[]}

let new_name _ = Ident ( "proc_" ^ (string_of_int (new_index ()))) 

let add_stmt f (s: stmt) = !f.bl.stmts <- (!f.bl.stmts @ [s]) 

let add_def f d t = !f.bl.defs <- (DefSet.add (d,t) !f.bl.defs)

let commit_block f = 
  !f.pr.blocks <- !f.pr.blocks@[!f.bl]; 
  !f.bl <- {!f.bl with stmts = []} 

let params_call defs = List.map (fun (d, t) -> Expr_Var d) (DefSet.to_list defs) 

let add_procs f p = !f.procs <- !f.procs @ p 

let commit_proc f = 
    let n_name = new_name () in
    commit_block f; 
    !f.procs <- !f.procs@[!f.pr] ; 
    !f.pr <- {name = n_name ; params = !f.bl.defs; blocks = [{!f.bl with stmts = []}]}

let rec split_stmt s (f: funwork ref) : unit =  
  (match s with
    | Stmt_VarDeclsNoInit(ty, vs, loc) -> add_stmt f s  ; List.iter (fun d -> add_def f d ty ) vs 
    | Stmt_VarDecl(ty, v, e, loc) -> add_stmt f s  ; add_def f v ty 
    | Stmt_ConstDecl(ty, v, e, loc) -> add_stmt f s ; add_def f v ty  
    | Stmt_FunReturn(e, loc) ->add_stmt f s ; commit_block f 
    | Stmt_ProcReturn(loc) ->add_stmt f s ; commit_block f 
    | Stmt_If(c, thensl, elsesl, ff, loc) ->
        commit_block f ;
        (* unconditionally split the ifcond subblocks into separate blocks *)
        let rec iter = function
        | S_Elsif_Cond(c,b)::xs ->
            S_Elsif_Cond(c, split_stmts b f)::(iter xs)
        | [] -> [] in
        let thennew = (split_stmts thensl f) in
        let elsenew = iter elsesl in
        let ffnew = split_stmts ff f in
        add_stmt f (Stmt_If(c, thennew, elsenew, ffnew, loc))
    | _ -> ()) 

and split_stmts (ss: stmt list) (f: funwork ref) : stmt list = 
  match ss with
    | [] -> ss
    | xs -> 
      let nf = ref (init_fn (new_name ()) !f.bl.defs) in
      let cf = !nf.pr in
      List.iter (fun s -> split_stmt s nf) xs; commit_proc nf; (add_procs f !nf.procs) ;
      [Stmt_TCall(cf.name, [], (params_call cf.params), Unknown)]


let rec write_stmt s st =
  match s with
  | Stmt_VarDeclsNoInit(ty, vs, loc) ->
      add_decl_scope st; 
      write_line "{\n" st;
      let e = default_value ty st in
      List.iter (fun v -> write_ref v ty e st) vs 

  | Stmt_VarDecl(ty, v, e, loc) ->
      add_decl_scope st; 
      write_line "{\n" st;
      let e = prints_expr e st in
      write_ref v ty e st

  | Stmt_ConstDecl(ty, v, e, loc) ->
      add_decl_scope st; 
      write_line "{\n" st;
      let e = prints_expr e st in
      write_let v ty e st

  | Stmt_Assign(l, r, loc) ->
      let e = prints_expr r st in
      write_assign l e st

  | Stmt_TCall(f, tes, es, loc) ->
      update_funcalls (funcall_to_sig (name_of_ident f) tes es) st.called_fun  ;
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
      write_line (String.concat "" (List.init (get_decl_scope st) (fun _ -> "}"))) st;
      clear_decl_scope st;
      dec_depth st
  | x::xs ->
      write_line "// new stmt \n" st;
      write_stmt x st;
      List.iter (fun s ->
        write_seq st;
        write_stmt s st
      ) xs;
      write_line (String.concat "" (List.init (get_decl_scope st) (fun _ -> "}"))) st;
      clear_decl_scope st;
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

let init_st : st = { indent = 0; skip_seq=false; called_fun=StringTbl.create 100; output_fun=StringTbl.create 100; oc=stdout; decl_scopes = IntTbl.empty; definitions = DefSet.empty} 
let rinit_st oc st : st =  {st with indent = 0; skip_seq=false;  oc=oc;  definitions = DefSet.empty} 

let build_args (tys: ((ty * ident)  list)) targs args =
  let targs =  List.map (fun t -> name_of_ident t) targs in 
  let ta = List.map (fun (t, i) -> (name_of_ident i) ^ ": " ^ (prints_arg_type t)) tys in
  if List.length targs = 0 && List.length args = 0 then "()"
  else "(" ^ (String.concat "," (targs@ta)) ^ ")" 



  

let print_write_fn (name: AST.ident) (ret_tyo, argtypes, targs, args, _, body) st = 
  update_funcalls {name=(name_of_ident name); 
    targs=(List.map (fun _ -> Some (Type_Constructor (Ident "integer"))) targs); 
    args = List.map (fun (t, _) -> Some t) (argtypes)} (st.output_fun) ;
  let args = build_args argtypes targs args in
  let ret = prints_ret_type ret_tyo in
  Printf.fprintf st.oc "def %s %s : %s = {\n" (name_of_ident name) args ret;
  write_stmts body st;
  Printf.fprintf st.oc "\n}\n"



let to_binding (p:proc) : (AST.ident * ('a option) * ((ty * ident) list) * (ident list)  * 'b * (stmt list) ) = 
  let argtypes : (ty * ident ) list = List.map (fun (b,a) -> (a,b)) (DefSet.to_list p.params) in
  let args = (List.map snd (DefSet.to_list p.params)) in
  (p.name, None,  argtypes, [], args, List.concat (List.map (fun f -> f.stmts) p.blocks) ) 

let write_fn (name: AST.ident) (ret_tyo, argtypes, targs, args, _, body) st = 
  let bs = DefSet.of_list (List.map (fun (a,t) -> (t,a)) argtypes) in
  let b = ref @@ init_fn name bs in
  let nb = split_stmts body b in
  print_write_fn name (ret_tyo, argtypes, targs, args, (), nb) st;
  List.iter (fun p -> 
    let nm, rt, art, targs, args , body = to_binding p in
    print_write_fn (nm) (rt,art,targs,args,(),body) st
  ) !b.procs


(* Write an instruction file, containing just the behaviour of one instructions *)
let write_instr_file fn fnsig dir st =
  let m = name_of_FIdent fn in
  let path = dir ^ "/" ^ m ^ ".scala" in
  let oc = open_out path in
  let st = rinit_st oc st in
  write_preamble global_imports global_opens st;
  write_fn fn fnsig st;
  close_out oc;
  name_of_FIdent fn


(* Write the decoder file - should depend on all of the above *)
let write_decoder_file fn fnsig deps dir st =
  let m = "aslpOffline" in
  let path = dir ^ "/" ^ m ^ ".scala" in
  let oc = open_out path in
  let st = rinit_st oc st in
  write_preamble global_imports (global_opens) st;
  write_fn fn fnsig st;
  write_epilogue fn st;
  close_out oc;
  m 

(* Write the test file, containing all decode tests *)
let write_test_file tests dir st =
  let m = "decode_tests" in
  let path = dir ^ "/" ^ m ^".scala" in
  let oc = open_out path in
  let st = rinit_st oc st in
  write_preamble global_imports (global_opens) st;
  Bindings.iter (fun i s -> write_fn i s st) tests;
  close_out oc;
  m

let printfundiff st = 
  print_endline (String.concat ("") (List.map (fun _ -> "-") (List.init 80 (fun x -> x + 1))));
  print_endline "Functions called and not generated:\n" ;
  let print_fsig (oc:out_channel) (f:fsig) = 
    let totypename l = ((List.map (function 
          | Some t -> prints_arg_type  t
          | None -> "?"
        ) l))
    in
    let withparamname p l : string list = ((List.mapi (fun i s -> p ^ (Int.to_string i) ^ ": " ^ s) (totypename l))) in 
    Printf.sprintf "%s ( %s )" f.name (String.concat ", " (List.sort String.compare (withparamname "targ" f.targs)@(withparamname "arg" f.args))) in
  let diff = Seq.filter 
     (fun f -> (StringTbl.find_opt st.output_fun f) == None) 
    (StringTbl.to_seq_keys st.called_fun) in
  List.iter (print_endline) (List.sort String.compare (List.of_seq (Seq.map (fun f -> print_fsig stdout (StringTbl.find st.called_fun f)) diff)))


(* Write all of the above, expecting Utils.ml to already be present in dir *)
(* decoder fun decodef fnsig, test funs, instruction funs, output directory  

   (ast_utils functions for accessing parts of function signature tuple)

  let files = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig dir)::acc) fns [] in
  write_decoder_file dfn dfnsig files dir |> ignore
   *)


let run (dfn: AST.ident) dfnsig tests (fns : (ty option * (ty * ident) list * ident list * 'a list * 'b * stmt list) Bindings.t) dir : unit =
  let st = init_st  in
  let files = Bindings.fold (fun fn fnsig acc -> (write_instr_file fn fnsig dir st)::acc) fns [] in
  let files = (write_test_file tests dir st)::files in
  write_decoder_file dfn dfnsig files dir st |> ignore ; 
  printfundiff st ;
  ()



