package viper.silver.ast.utility

import viper.silver.ast.{BackendFunc, BackendType, Bool, Domain, DomainFunc, Int, LocalVarDecl}

/**
  * A factory for fixed-size bitvectors that offers convenient access to bitvector types, as well as
  * function definitions for unary and binary functions on bitvectors, as well as conversions from and
  * to integers.
  */
case class BVFactory(size: Int) {
  lazy val interpretations = Map("Boogie" -> s"bv${size}", "SMTLIB" -> s"(_ BitVec ${size})")
  lazy val typ = BackendType(name, interpretations)
  lazy val name = s"BitVectorDomain${size}"

  def constructDomain(functions: Seq[DomainFunc]) = Domain(name, functions, Seq(), Seq(), Some(interpretations))()

  /**
   * bit vector bitwise xor
   */
  def xor(name: String) = BackendFunc(name, "bvxor", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector bitwise bvxnor
   */
  def xnor(name: String) = BackendFunc(name, "bvxnor", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector bitwise and
   */
  def and(name: String) = BackendFunc(name, "bvand", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector bitwise nand
   */
  def nand(name: String) = BackendFunc(name, "bvnand", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector bitwise or
   */
  def or(name: String) = BackendFunc(name, "bvor", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector bitwise nor
   */
  def nor(name: String) = BackendFunc(name, "bvnor", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector addition
   */
  def add(name: String) = BackendFunc(name, "bvadd", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector subtraction
   */
  def sub(name: String) = BackendFunc(name, "bvsub", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector multiplication
   */
  def mul(name: String) = BackendFunc(name, "bvmul", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector signed modulo
   */
  def smod(name: String) = BackendFunc(name, "bvsmod", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector unsigned division
   */
  def udiv(name: String) = BackendFunc(name, "bvudiv", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector unsigned remainder
   */
  def urem(name: String) = BackendFunc(name, "bvurem", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector signed remainder
   */
  def srem(name: String) = BackendFunc(name, "bvsrem", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector shift left
   */
  def shl(name: String) = BackendFunc(name, "bvshl", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector unsigned (logical) shift right
   */
  def lshr(name: String) = BackendFunc(name, "bvlshr", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  /**
   * bit vector signed (arithmetical) shift right
   */
  def ashr(name: String) = BackendFunc(name, "bvashr", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()

  /**
   * bit vector bitwise not
   */
  def not(name: String) = BackendFunc(name, "bvnot", name, typ, Seq(LocalVarDecl("x", typ)()))()
  /**
   * bit vector unary minus
   */
  def neg(name: String) = BackendFunc(name, "bvneg", name, typ, Seq(LocalVarDecl("x", typ)()))()

  def from_int(name: String) = BackendFunc(name, s"(_ int2bv ${size})", name, typ, Seq(LocalVarDecl("x", Int)()))()
  def to_int(name: String) = BackendFunc(name, s"(_ bv2int ${size})", name, Int, Seq(LocalVarDecl("x", typ)()))()
  def from_nat(name: String) = BackendFunc(name, s"(_ nat2bv ${size})", name, typ, Seq(LocalVarDecl("x", Int)()))()
  def to_nat(name: String) = BackendFunc(name, s"(_ bv2nat ${size})", name, Int, Seq(LocalVarDecl("x", typ)()))()
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
  lazy val interpretations = Map("Boogie" -> s"float${mant}e${exp}", "SMTLIB" -> s"(_ FloatingPoint ${exp} ${mant})")
  lazy val typ = BackendType(name, interpretations)
  lazy val name = s"FloatDomain${mant}e${exp}"

  def constructDomain(functions: Seq[DomainFunc]) = Domain(name, functions, Seq(), Seq(), Some(interpretations))()

  def neg(name: String) = BackendFunc(name, "fp.neg", name, typ, Seq(LocalVarDecl("x", typ)()))()
  def abs(name: String) = BackendFunc(name, "fp.abs", name, typ, Seq(LocalVarDecl("x", typ)()))()

  def add(name: String) = BackendFunc(name, s"fp.add ${roundingMode}", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def sub(name: String) = BackendFunc(name, s"fp.sub ${roundingMode}", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def mul(name: String) = BackendFunc(name, s"fp.mul ${roundingMode}", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def div(name: String) = BackendFunc(name, s"fp.div ${roundingMode}", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()

  def min(name: String) = BackendFunc(name, s"fp.min", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def max(name: String) = BackendFunc(name, s"fp.max", name, typ, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()

  def eq(name: String) = BackendFunc(name, s"fp.eq", name, Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def leq(name: String) = BackendFunc(name, s"fp.leq", name, Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def geq(name: String) = BackendFunc(name, s"fp.geq", name, Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def lt(name: String) = BackendFunc(name, s"fp.lt", name, Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()
  def gt(name: String) = BackendFunc(name, s"fp.gt", name, Bool, Seq(LocalVarDecl("x", typ)(), LocalVarDecl("y", typ)()))()

  def isZero(name: String) = BackendFunc(name, s"fp.isZero", name, Bool, Seq(LocalVarDecl("x", typ)()))()
  def isInfinite(name: String) = BackendFunc(name, s"fp.isInfinite", name, Bool, Seq(LocalVarDecl("x", typ)()))()
  def isNaN(name: String) = BackendFunc(name, s"fp.isNaN", name, Bool, Seq(LocalVarDecl("x", typ)()))()
  def isNegative(name: String) = BackendFunc(name, s"fp.isNegative", name, Bool, Seq(LocalVarDecl("x", typ)()))()
  def isPositive(name: String) = BackendFunc(name, s"fp.isPositive", name, Bool, Seq(LocalVarDecl("x", typ)()))()

  def from_bv(name: String) = BackendFunc(name, s"(_ to_fp ${exp} ${mant}) ", name, typ, Seq(LocalVarDecl("x", BVFactory(mant+exp).typ)()))()
  def to_bv(name: String) = BackendFunc(name, s"(_ fp.to_sbv ${exp+mant}) ${roundingMode} ", name, BVFactory(mant+exp).typ, Seq(LocalVarDecl("x", typ)()))()
}
