(****************************************************************
 * CPU interface
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

type gen_backend =
        | OCaml 
        | Scala

type cpu = {
    env      : Eval.Env.t;
    denv     : Dis.env;
    reset    : unit -> unit;
    step     : unit -> unit;
    getPC    : unit -> Primops.bigint;
    setPC    : Primops.bigint -> unit;
    elfwrite : Int64.t -> char -> unit;
    opcode   : string -> Primops.bigint -> unit;
    sem      : string -> Primops.bigint -> unit;
    gen      : string -> gen_backend -> ?directory:string ->  string -> unit
}

val mkCPU : Eval.Env.t -> Dis.env -> cpu

(****************************************************************
 * End
 ****************************************************************)
