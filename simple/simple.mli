(****************************************************************
 *  Simple cacheable interface to ASLp 
 *
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

open LibASL

type retrieve_env = 
  {
    decls: Asl_ast.declaration list;
    eval_env: Eval.Env.t;
    id: bytes;
  }
;; 

val environment : string option ->  string list -> retrieve_env
