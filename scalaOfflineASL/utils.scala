package aslloader

import ir._
import analysis.BitVectorEval._

/**
f_SignExtend ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BigInt )
f_ZeroExtend ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BigInt )
f_add_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_and_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_append_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_asr_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: ? )
f_cvt_bits_uint ( targ0: BigInt, arg0: BitVecLiteral )
f_decl_bool ( arg0: ? )
f_decl_bv ( arg0: ?, arg1: BigInt )
f_eq_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_gen_BFAdd ( arg0: ?, arg1: ? )
f_gen_BFMul ( arg0: ?, arg1: ? )
f_gen_FPAdd ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPCompare ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ? )
f_gen_FPCompareEQ ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPCompareGE ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPCompareGT ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPConvert ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPConvertBF ( arg0: ?, arg1: ?, arg2: ? )
f_gen_FPDiv ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMax ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMaxNum ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMin ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMinNum ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMul ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPMulAdd ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ? )
f_gen_FPMulAddH ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ? )
f_gen_FPMulX ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPRSqrtStepFused ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_FPRecipEstimate ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_FPRecipStepFused ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_FPRecpX ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_FPRoundInt ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ? )
f_gen_FPRoundIntN ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ? )
f_gen_FPSqrt ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_FPSub ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FPToFixed ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ?, arg4: ? )
f_gen_FPToFixedJS_impl ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_FixedToFP ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ?, arg2: ?, arg3: ?, arg4: ? )
f_gen_Mem_read ( targ0: BigInt, arg0: ?, arg1: ?, arg2: ? )
f_gen_SignExtend ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_ZeroExtend ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_add_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_and_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_and_bool ( arg0: ?, arg1: ? )
f_gen_append_bits ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_array_load ( arg0: ?, arg1: BigInt )
f_gen_asr_bits ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_bit_lit ( targ0: BigInt, arg0: BitVecLiteral )
f_gen_bool_lit ( arg0: Boolean )
f_gen_branch ( arg0: ? )
f_gen_cvt_bits_uint ( targ0: BigInt, arg0: ? )
f_gen_cvt_bool_bv ( arg0: ? )
f_gen_eor_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_eq_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_eq_enum ( arg0: ?, arg1: ? )
f_gen_int_lit ( arg0: BigInt )
f_gen_load ( arg0: ? )
f_gen_lsl_bits ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_lsr_bits ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_mul_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_ne_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_not_bits ( targ0: BigInt, arg0: ? )
f_gen_not_bool ( arg0: ? )
f_gen_or_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_or_bool ( arg0: ?, arg1: ? )
f_gen_replicate_bits ( targ0: BigInt, targ1: BigInt, arg0: ?, arg1: ? )
f_gen_sdiv_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_sle_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_slice ( arg0: ?, arg1: BigInt, arg2: BigInt )
f_gen_slt_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_gen_sub_bits ( targ0: BigInt, arg0: ?, arg1: ? )
f_lsl_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: ? )
f_lsr_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: ? )
f_mul_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_ne_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_not_bits ( targ0: BigInt, arg0: BitVecLiteral )
f_or_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_replicate_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BigInt )
f_sle_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
f_slt_bits ( targ0: BigInt, arg0: ?, arg1: BitVecLiteral )
f_sub_bits ( targ0: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral )
 */

class Mutable[T](var v: T)

def extract(x: BigInt, sz: BigInt) = x % (BigInt(2).pow((sz + 1).toInt))

def mkBits(n: Int, y: BigInt): BitVecLiteral = {
  require(n >= 0)
  BitVecLiteral(extract(y, n), n)
}

def bvextract(e: BitVecLiteral, lo: BigInt, width: BigInt, idk: BigInt) :BitVecLiteral = smt_extract(lo.toInt, (lo + width - 1).toInt, e)


def f_eq_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : Boolean  = (smt_bveq(x,y) == TrueLiteral)

def f_ne_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : Boolean  = (smt_bveq(x,y) == FalseLiteral)

def f_add_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvadd(x,y))

def f_sub_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvsub(x,y))

def f_mul_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvmul(x,y))

def f_and_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvand(x,y))

def f_or_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvor(x,y))

def f_eor_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvxor(x,y))

def f_not_bits(t: BigInt, x: BitVecLiteral) : BitVecLiteral  = (smt_bvnot(x))

def f_slt_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : Boolean = (TrueLiteral == (smt_bvslt(x,y)))

def f_sle_bits(t: BigInt, x: BitVecLiteral, y: BitVecLiteral) : Boolean = (TrueLiteral == (smt_bvsle(x,y)))


def f_zeros_bits(w: BigInt) : BitVecLiteral =  BitVecLiteral(0, w.toInt)

def f_ones_bits(w: BigInt) : BitVecLiteral =  BitVecLiteral(BigInt(2).pow(w.toInt) - 1, w.toInt)


def f_ZeroExtend(t0: BigInt, t1: BigInt, n: BitVecLiteral, x: BigInt) : BitVecLiteral = smt_zero_extend(n.value.toInt, BitVecLiteral(x, t1.toInt))

def f_SignExtend(t0: BigInt, t1: BigInt, n: BitVecLiteral, x: BigInt) : BitVecLiteral = smt_sign_extend(n.value.toInt, BitVecLiteral(x, t1.toInt))

def f_asr_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral) : BitVecLiteral = throw NotImplementedError("func not implemented")

def f_lsl_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral) : BitVecLiteral = throw NotImplementedError("func not implemented")

def f_lsr_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral) : BitVecLiteral = throw NotImplementedError("func not implemented")




def f_replicate_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BigInt ) : BitVecLiteral = throw NotImplementedError("func not implemented")

def f_append_bits ( targ0: BigInt, targ1: BigInt, arg0: BitVecLiteral, arg1: BitVecLiteral ) : BitVecLiteral = throw NotImplementedError("func not implemented")


def f_cvt_bits_uint ( targ0: BigInt, arg0: BitVecLiteral ) : BigInt = throw NotImplementedError("func not implemented")

def f_decl_bool ( arg0: String ) : Expr = LocalVar(arg0, BoolType)
def f_decl_bv ( arg0: String , arg1: BigInt ) : Expr = LocalVar(arg0, BitVecType(arg1.toInt))


def f_gen_BFAdd ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_BFMul ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPAdd ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPCompare ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPCompareEQ ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPCompareGE ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPCompareGT ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPConvert ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPConvertBF ( arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPDiv ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMax ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMaxNum ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMin ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMinNum ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMul ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMulAdd ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMulAddH ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPMulX ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRSqrtStepFused ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRecipEstimate ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRecipStepFused ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRecpX ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRoundInt ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPRoundIntN ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPSqrt ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPSub ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPToFixed ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr, arg4: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FPToFixedJS_impl ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_FixedToFP ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr, arg4: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_Mem_read ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_SignExtend ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_ZeroExtend ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_add_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_and_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_and_bool ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_append_bits ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_array_load ( arg0: Expr, arg1: BigInt ): Expr = throw NotImplementedError("func not implemented")
def f_gen_asr_bits ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_bit_lit ( targ0: BigInt, arg0: BitVecLiteral ): Expr = throw NotImplementedError("func not implemented")
def f_gen_bool_lit ( arg0: Boolean ): Expr = throw NotImplementedError("func not implemented")

def f_gen_branch ( arg0: Expr ): (Expr, Expr, Expr) = throw NotImplementedError("func not implemented")

def f_gen_cvt_bits_uint ( targ0: BigInt, arg0: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_cvt_bool_bv ( arg0: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_eor_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_eq_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_eq_enum ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_int_lit ( arg0: BigInt ): Expr = throw NotImplementedError("func not implemented")

def f_gen_store ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_load ( arg0: Expr ): Expr = throw NotImplementedError("func not implemented")

def f_gen_lsl_bits ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_lsr_bits ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_mul_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_ne_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_not_bits ( targ0: BigInt, arg0: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_not_bool ( arg0: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_or_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_or_bool ( arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_replicate_bits ( targ0: BigInt, targ1: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_sdiv_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_sle_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_slice ( arg0: Expr, arg1: BigInt, arg2: BigInt ): Expr = throw NotImplementedError("func not implemented")
def f_gen_slt_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")
def f_gen_sub_bits ( targ0: BigInt, arg0: Expr, arg1: Expr ): Expr = throw NotImplementedError("func not implemented")


def f_AtomicEnd () : Expr = Register("ATOMICSTART", BoolType)
def f_AtomicStart () : Expr = Register("ATOMICSTART", BoolType)
def f_gen_AArch64_MemTag_set ( arg0: Expr, arg1: Expr, arg2: Expr ) : Expr = throw NotImplementedError("func not implemented")

def f_gen_Mem_set ( targ0: BigInt, arg0: Expr, arg1: Expr, arg2: Expr, arg3: Expr ): Expr  = throw NotImplementedError("func not implemented")

def f_gen_array_store ( arg0: Expr, arg1: BigInt, arg2: Expr) : Expr = throw NotImplementedError("func not implemented")
def f_gen_assert ( arg0: Expr ) = throw NotImplementedError("func not implemented")
def f_switch_context ( arg0: Expr ) = throw NotImplementedError("func not implemented")


def v_PSTATE_C = Mutable(Register("PSTATE.C", BoolType)) // Expr_Field(Expr_Var(Ident "PSTATE"), Ident "C")
def v_PSTATE_Z = Mutable(Register("PSTATE.Z", BoolType)) // Expr_Field(Expr_Var(Ident "PSTATE"), Ident "Z")
def v_PSTATE_V = Mutable(Register("PSTATE.V", BoolType)) // Expr_Field(Expr_Var(Ident "PSTATE"), Ident "V")
def v_PSTATE_N = Mutable(Register("PSTATE.N", BoolType)) // Expr_Field(Expr_Var(Ident "PSTATE"), Ident "N")
def v__PC      = Mutable(Register("_PC", IntType)) // Expr_Var(Ident "_PC")
def v__R       = Mutable(Register("_R", IntType))
def v__Z       = Mutable(Register("_Z", BoolType))
def v_SP_EL0   = Mutable(Register("SP_EL0", BoolType))
def v_FPSR     = Mutable(Register("FPSR", BoolType))
def v_FPCR     = Mutable(Register("FPCR", BoolType))

def v_PSTATE_BTYPE =  Mutable(Register("PSTATE.BTYPE", BoolType)) // Expr_Field(Expr_Var(Ident "PSTATE"), Ident "BTYPE")
def v_BTypeCompatible = Mutable(Register("BTypeCompatible", BoolType)) // Expr_Var (Ident "BTypeCompatible")
def v___BranchTaken = Mutable(Register("__BranchTaken", BoolType))
def v_BTypeNext = Mutable(Register("BTypeNext", BoolType))
def v___ExclusiveLocal = Mutable(Register("__ExclusiveLocal", BoolType))


