package viper.silver.ast.utility

import viper.silver.ast.{Bool, Int, LocalVarDecl, BackendFunc, BackendType}

/**
  * A factory for fixed-size bitvectors that offers convenient access to bitvector types, as well as
  * function definitions for unary and binary functions on bitvectors, as well as conversions from and
  * to integers.
  */
case class BVFactory(size: Int) {
  lazy val typ = BackendType(s"bv${size}", s"(_ BitVec ${size})")

  def xor(name: String) = BackendFunc(name, "bvxor", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def and(name: String) = BackendFunc(name, "bvand", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def or(name: String) = BackendFunc(name, "bvor", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def add(name: String) = BackendFunc(name, "bvadd", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def mul(name: String) = BackendFunc(name, "bvmul", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def shl(name: String) = BackendFunc(name, "bvshl", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def shr(name: String) = BackendFunc(name, "bvshr", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))

  def not(name: String) = BackendFunc(name, "bvnot", typ, Seq(LocalVarDecl("x", typ)()))
  def neg(name: String) = BackendFunc(name, "bvneg", typ, Seq(LocalVarDecl("x", typ)()))

  def from_int(name: String) = BackendFunc(name, s"(_ int2bv ${size})", typ, Seq(LocalVarDecl("x", Int)()))
  def to_int(name: String) = BackendFunc(name, s"(_ bv2int ${size})", Int, Seq(LocalVarDecl("x", typ)()))
  def from_nat(name: String) = BackendFunc(name, s"(_ nat2bv ${size})", typ, Seq(LocalVarDecl("x", Int)()))
  def to_nat(name: String) = BackendFunc(name, s"(_ bv2nat ${size})", Int, Seq(LocalVarDecl("x", typ)()))
}

/**
  * Rounding modes for floating point operations.
  */
object RoundingMode extends Enumeration {
  type RoundingMode = Value
  val RNE, RNA, RTP, RTN, RTZ = Value
}
import RoundingMode._

/**
  * A factory for IEEE floating point numbers with "exp" bits for the exponent, "mant" bits for the significant,
  * including the hidden bit, and a given rounding mode for all operations that use one.
  * Offers access to types, unary and binary operations, comparisons, and conversions from and to
  * bitvectors of size exp + mant.
  */
case class FloatFactory(mant: Int, exp: Int, roundingMode: RoundingMode) {

  lazy val typ = BackendType(s"float${mant}e${exp}", s"(_ FloatingPoint ${exp} ${mant})")

  def neg(name: String) = BackendFunc(name, "fp.neg", typ, Seq(LocalVarDecl("x", typ)()))
  def abs(name: String) = BackendFunc(name, "fp.abs", typ, Seq(LocalVarDecl("x", typ)()))

  def add(name: String) = BackendFunc(name, s"fp.add ${roundingMode}", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def sub(name: String) = BackendFunc(name, s"fp.sub ${roundingMode}", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def mul(name: String) = BackendFunc(name, s"fp.mul ${roundingMode}", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def div(name: String) = BackendFunc(name, s"fp.div ${roundingMode}", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))

  def min(name: String) = BackendFunc(name, s"fp.min", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def max(name: String) = BackendFunc(name, s"fp.max", typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))

  def eq(name: String) = BackendFunc(name, s"fp.eq", Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def leq(name: String) = BackendFunc(name, s"fp.leq", Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def geq(name: String) = BackendFunc(name, s"fp.geq", Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def lt(name: String) = BackendFunc(name, s"fp.lt", Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))
  def gt(name: String) = BackendFunc(name, s"fp.gt", Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))

  def isZero(name: String) = BackendFunc(name, s"fp.isZero", Bool, Seq(LocalVarDecl("x", typ)()))
  def isInfinite(name: String) = BackendFunc(name, s"fp.isInfinite", Bool, Seq(LocalVarDecl("x", typ)()))
  def isNaN(name: String) = BackendFunc(name, s"fp.isNaN", Bool, Seq(LocalVarDecl("x", typ)()))
  def isNegative(name: String) = BackendFunc(name, s"fp.isNegative", Bool, Seq(LocalVarDecl("x", typ)()))
  def isPositive(name: String) = BackendFunc(name, s"fp.isPositive", Bool, Seq(LocalVarDecl("x", typ)()))

  def from_bv(name: String) = BackendFunc(name, s"(_ to_fp ${exp} ${mant}) ", typ, Seq(LocalVarDecl("x", BVFactory(mant+exp).typ)()))
  def to_bv(name: String) = BackendFunc(name, s"(_ fp.to_sbv ${exp+mant}) ${roundingMode} ", BVFactory(mant+exp).typ, Seq(LocalVarDecl("x", typ)()))
}