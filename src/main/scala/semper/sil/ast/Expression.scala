package semper.sil.ast

import org.kiama.output._
import utility.Consistency
import utility.Transformer

/** Expressions. */
sealed trait Exp extends Node with Typed with Positioned with Infoed with PrettyExpression {

  /**
   * Transforms an expression using the function `f`;  if `f` returns `Some(e)`, then the previous expression
   * is replaced by e, and otherwise the previous expression is reused.
   * The function `f` must produce expressions that are valid in the given context.  For instance, it cannot
   * replace an integer literal by a boolean literal.
   */
  def transform(f: Exp => Option[Exp]): Exp = Transformer.transform(this, f)
}


// --- Simple integer and boolean expressions (binary and unary operations, literals)

// Arithmetic expressions
case class Add(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PlusOp)
case class Sub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(MinusOp)
case class Mul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(TimesOp)
case class Div(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(DividedOp)
case class Mod(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(ModuloOp)

// Integer comparison expressions
case class LtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LtOp)
case class LeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LeOp)
case class GtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GtOp)
case class GeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GeOp)

// Equality and non-equality (defined for all types)
case class EqCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends EqualityCmp("==")
case class NeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends EqualityCmp("!=")

/** Integer literal. */
case class IntLit(i: BigInt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  lazy val typ = Int
}

/** Integer negation. */
case class Neg(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainUnExp(NegOp)

// Boolean expressions
case class Or(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(OrOp)
case class And(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(AndOp)
case class Implies(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(ImpliesOp)

/** Boolean literals. */
sealed abstract class BoolLit(val value: Boolean) extends Exp {
  lazy val typ = Bool
}
object BoolLit {
  def unapply(b: BoolLit) = Some(b.value)
  def apply(b: Boolean)(pos: Position = NoPosition, info: Info = NoInfo) = if (b) TrueLit()(pos, info) else FalseLit()(pos, info)
}
case class TrueLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends BoolLit(true)
case class FalseLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends BoolLit(false)

/** Boolean negation. */
case class Not(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainUnExp(NotOp)

case class NullLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  lazy val typ = Ref
}

// --- Accessibility predicates

/** A common trait for accessibility predicates. */
sealed trait AccessPredicate extends Exp {
  require(perm isSubtype Perm)
  def loc: LocationAccess
  def perm: Exp
  lazy val typ = Bool
}
object AccessPredicate {
  def unapply(a: AccessPredicate) = Some((a.loc, a.perm))
}

/** An accessibility predicate for a field location. */
case class FieldAccessPredicate(loc: FieldAccess, perm: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AccessPredicate

/** An accessibility predicate for a predicate location. */
case class PredicateAccessPredicate(loc: PredicateAccess, perm: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AccessPredicate

// --- Permissions

/** A common trait for expressions of type permission. */
sealed trait PermExp extends Exp {
  override lazy val typ = Perm
}

/** An abstract read permission. Has an unknown local value, but it has the same value inside one method and its contracts. */
case class ReadPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

/** A wildcard permission. Has an unknown value, but there are no guarantees that it will be the same inside one method. */
case class WildCard()(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

/** The full permission. */
case class FullPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractConcretePerm(1, 1)

/** No permission. */
case class NoPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractConcretePerm(0, 1)

/** An epsilon permission. */
case class EpsilonPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

/** A concrete fraction as permission amount. */
case class ConcretePerm(override val numerator: BigInt, override val denominator: BigInt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractConcretePerm(numerator, denominator) with PrettyBinaryExpression {
  lazy val priority = 0 // always at parenthesis
  lazy val fixity = Infix(LeftAssoc)
  lazy val left: PrettyExpression = IntLit(numerator)()
  lazy val op = "/"
  lazy val right: PrettyExpression = IntLit(denominator)()
}

/** The permission currently held for a given location. */
case class CurrentPerm(loc: LocationAccess)(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

// Arithmetic expressions
case class PermAdd(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermPlusOp) with PermExp
case class PermSub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermMinusOp) with PermExp
case class PermMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermTimesOp) with PermExp
case class PermIntMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(IntPermTimesOp) with PermExp

// Comparison expressions
case class PermLtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LtOp)
case class PermLeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LeOp)
case class PermGtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GtOp)
case class PermGeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GeOp)


// --- Function application (domain and normal)

/** Function application. */
case class FuncApp(func: Function, rcv: Exp, args: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends FuncLikeApp with RcvNode

/** User-defined domain function application. */
case class DomainFuncApp(func: DomainFunc, args: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractDomainFuncApp


// --- Field and predicate accesses

/** A common trait for expressions accessing a location. */
sealed trait LocationAccess extends Exp {
  def loc: Location
  def rcv: Exp
}

/** A field access expression. */
case class FieldAccess(rcv: Exp, field: Field)(val pos: Position = NoPosition, val info: Info = NoInfo) extends LocationAccess with RcvNode {
  lazy val loc = field
  lazy val typ = field.typ
}

/** A predicate access expression. */
case class PredicateAccess(rcv: Exp, predicate: Predicate)(val pos: Position = NoPosition, val info: Info = NoInfo) extends LocationAccess with RcvNode {
  lazy val loc = predicate
  lazy val typ = Pred
}


// --- Conditional expression

/** A conditional expressions. */
case class CondExp(cond: Exp, thn: Exp, els: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  require(cond isSubtype Bool)
  require(thn.typ == els.typ)
  lazy val typ = Bool
}


// --- Unfolding expression

case class Unfolding(acc: PredicateAccessPredicate, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  lazy val typ = exp.typ
}

// --- Old expression

case class Old(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends UnExp {
  lazy val typ = exp.typ
}


// --- Quantifications

/** A common trait for quantified expressions. */
sealed trait QuantifiedExp extends Exp {
  require(exp isSubtype Bool)
  def variable: LocalVarDecl
  def exp: Exp
  lazy val typ = Bool
}

/** Universal quantification. */
case class Forall(variable: LocalVarDecl, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends QuantifiedExp

/** Existential quantification. */
case class Exists(variable: LocalVarDecl, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends QuantifiedExp


// --- Variables, this, result

/** A local variable, special or not (used both for declarations and usages). */
sealed trait AbstractLocalVar extends Exp {
  def name: String
  lazy val mutable = true
}
object AbstractLocalVar {
  def unapply(l: AbstractLocalVar) = Some(l.name)
}

/** A normal local variable. */
case class LocalVar(name: String)(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar {
  require(Consistency.validUserDefinedIdentifier(name))
}

/** A special local variable for the result of a function. */
case class Result()(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar {
  lazy val name = "result"
}

/** The `this` literal. */
case class ThisLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar {
  lazy val typ = Ref
  lazy val name = "this"
  override lazy val mutable = false
}


// --- Common functionality

/**
 * A common class for concrete permissions.  The name AbstractConcretePerm is used because it is an abstract superclass for concrete permissions.
 */
sealed abstract class AbstractConcretePerm(val numerator: BigInt, val denominator: BigInt) extends PermExp

/** Common ancestor of Domain Function applications and Function applications. */
sealed trait FuncLikeApp extends Exp with Call with Typed {
  def func: FuncLike
  lazy val callee = func
  lazy val typ = func.typ
}

/** Common superclass for domain functions with arbitrary parameters and return type, binary and unary operations are a special case. */
sealed trait AbstractDomainFuncApp extends FuncLikeApp {
  def func: AbstractDomainFunc
}

/**
 * A common class for equality and inequality comparisons.  Note that equality is defined for
 * all types, and therefore is not a domain function and does not belong to a domain.
 */
sealed abstract class EqualityCmp(val op: String) extends BinExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  lazy val priority = 13
  lazy val fixity = Infix (NonAssoc)
  lazy val typ = Bool
}

/** Expressions with a unary or binary operator. */
sealed trait DomainOpExp extends AbstractDomainFuncApp {
  def func: Op
  def op = func.op
  def fixity = func.fixity
  def priority = func.priority
}

/** Binary expressions of any kind (whether or not they belong to a domain). */
sealed trait BinExp extends Exp with PrettyBinaryExpression {
  lazy val args = List(left, right)
  def left: Exp
  def right: Exp
}
object BinExp {
  def unapply(binExp: BinExp) = Some((binExp.left, binExp.right))
}

/** Unary expressions of any kind (whether or not they belong to a domain). */
sealed trait UnExp extends Exp {
  lazy val args = List(exp)
  def exp: Exp
}
object UnExp {
  def unapply(unExp: UnExp) = Some(unExp.exp)
}

/** Common superclass for binary expressions that belong to a domain (and thus have a domain operator). */
sealed abstract class DomainBinExp(val func: BinOp) extends BinExp with DomainOpExp

/** Common superclass for unary expressions that belong to a domain (and thus have a domain operator). */
sealed abstract class DomainUnExp(val func: UnOp) extends PrettyUnaryExpression with DomainOpExp with UnExp


