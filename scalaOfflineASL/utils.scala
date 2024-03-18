import ir._
package aslloader

import analysis.BitVectorEval.*

def extract(x: BigInt, sz: BigInt) =  x % (BigInt(2).pow(sz + 1))

def mkBits(n: Int, y: BigInt): BitVecLiteral = {
  require(n >= 0)
  BitVecLiteral(extract(y, n), n)
}

def bvextract(e: BitVecLiteral, lo: BigInt, width: BigInt) = smt_extract(lo, (lo + width - 1), e)


def f_eq_bits(x: BitVecLiteral, y: BitVecLiteral) : Boolean  = (smt_bveq(x,y) == TrueLiteral)

def f_ne_bits(x: BitVecLiteral, y: BitVecLiteral) : Boolean  = (smt_bveq(x,y) == FalseLiteral)

def f_add_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvadd(x,y))

def f_sub_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvsub(x,y))

def f_mul_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvmul(x,y))

def f_and_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvand(x,y))

def f_or_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvor(x,y))

def f_eor_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvxor(x,y))

def f_not_bits(x: BitVecLiteral) : BitVecLiteral  = (smt_bvnot(x))

def f_slt_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvslt(x,y))

def f_sle_bits(x: BitVecLiteral, y: BitVecLiteral) : BitVecLiteral  = (smt_bvsle(x,y))

def f_zeros_bits(w: BigInt) : BitVecLiteral =  BitVecLiteral(0, w.toInt)

def f_ones_bits(w: BigInt) : BitVecLiteral =  BitVecLiteral(BigInt(2).pow(w.toInt) - 1, w.toInt)

def f_replicate_bits(x: BigInt, y: BigInt) = BitVecLiteral(0, 0)

def f_append_bits(x: BigInt, y: BigInt) = BitVecLiteral(0, 0)

def f_ZeroExtend(n: BitVecLiteral, x: BitVecLiteral) = smt_zero_extend(n.value.toInt, x)

def f_SignExtend(n: BitVecLiteral, x: BitVecLiteral) = smt_sign_extend(n.value.toInt, x)



