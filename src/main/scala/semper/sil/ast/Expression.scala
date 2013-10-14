package semper.sil.ast

import org.kiama.output._
import semper.sil.ast.utility.{ Expressions, Consistency }

/** Expressions. */
sealed trait Exp extends Node with Typed with Positioned with Infoed with PrettyExpression {

  lazy val isPure = Expressions.isPure(this)

  /**
   * Returns a representation of this expression as it looks when it is used as a proof obligation, i.e. all
   * InhaleExhaleExp are replaced by the inhale part.
   */
  lazy val whenInhaling = Expressions.whenInhaling(this)

  /**
   * Returns a representation of this expression as it looks when it is used as a proof obligation, i.e. all
   * InhaleExhaleExp are replaced by the exhale part.
   */
  lazy val whenExhaling = Expressions.whenExhaling(this)

  /** Returns the subexpressions of this expression */
  lazy val subExps = Expressions.subExps(this)

  /**
   * Returns a conjunction of all proof obligations in this expression, e.g. rcv != null for all field accesses rcv.f,
   * we have permissions for all field accesses, the preconditions of all used functions are fulfilled etc.
   */
  lazy val proofObligations = Expressions.proofObligations(this)

}

// --- Simple integer and boolean expressions (binary and unary operations, literals)

// Arithmetic expressions
case class Add(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(AddOp)
case class Sub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(SubOp)
case class Mul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(MulOp)
case class Div(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(DivOp)
case class Mod(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(ModOp)

// Integer comparison expressions
case class LtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LtOp)
case class LeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(LeOp)
case class GtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GtOp)
case class GeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(GeOp)

// Equality and non-equality (defined for all types)
case class EqCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends EqualityCmp("==")
case class NeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends EqualityCmp("!=")

/** Integer literal. */
case class IntLit(i: BigInt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Literal {
  lazy val typ = Int
}

/** Integer negation. */
case class Neg(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainUnExp(NegOp)

// Boolean expressions
case class Or(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(OrOp) {
  Consistency.checkNoPositiveOnly(left)
  Consistency.checkNoPositiveOnly(right)
}
case class And(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(AndOp)

case class Implies(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(ImpliesOp) {
  Consistency.checkNoPositiveOnly(left)
}

case class MagicWand(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo)
    extends DomainBinExp(ImpliesOp)

/** Boolean negation. */
case class Not(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainUnExp(NotOp) {
  Consistency.checkNoPositiveOnly(exp)
}

/** Boolean literals. */
sealed abstract class BoolLit(val value: Boolean) extends Literal {
  lazy val typ = Bool
}
object BoolLit {
  def unapply(b: BoolLit) = Some(b.value)
  def apply(b: Boolean)(pos: Position = NoPosition, info: Info = NoInfo) = if (b) TrueLit()(pos, info) else FalseLit()(pos, info)
}
case class TrueLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends BoolLit(true)
case class FalseLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends BoolLit(false)

case class NullLit()(val pos: Position = NoPosition, val info: Info = NoInfo) extends Literal {
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

// --- Inhale exhale expressions.

/**
 * This is a special expression that is treated as `in` if it appears as an assumption and as `ex` if
 * it appears as a proof obligation.
 */
case class InhaleExhaleExp(in: Exp, ex: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  require(in.typ isSubtype Bool)
  require(ex.typ isSubtype Bool)
  val typ = Bool
}

// --- Permissions

/** A common trait for expressions of type permission. */
sealed trait PermExp extends Exp {
  override lazy val typ = Perm
}

/** A wild card permission. Has an unknown value, but there are no guarantees that it will be the same inside one method. */
case class WildcardPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

/** The full permission. */
case class FullPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractConcretePerm(1, 1)

/** No permission. */
case class NoPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractConcretePerm(0, 1)

/** An epsilon permission. */
case class EpsilonPerm()(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

/** A concrete fraction as permission amount. */
case class FractionalPerm(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(FracOp) with PermExp

/** The permission currently held for a given location. */
case class CurrentPerm(loc: LocationAccess)(val pos: Position = NoPosition, val info: Info = NoInfo) extends PermExp

// Arithmetic expressions
case class PermAdd(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermAddOp) with PermExp
case class PermSub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermSubOp) with PermExp
case class PermMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermMulOp) with PermExp
case class IntPermMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(IntPermMulOp) with PermExp

// Comparison expressions
case class PermLtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermLtOp)
case class PermLeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermLeOp)
case class PermGtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermGtOp)
case class PermGeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermGeOp)

// --- Function application (domain and normal)

/** Function application. */
case class FuncApp(func: Function, args: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends FuncLikeApp {
  args foreach Consistency.checkNoPositiveOnly

  /**
   * The precondition of this function application (i.e., the precondition of the function with
   * the arguments instantiated correctly).
   */
  lazy val pres = {
    func.pres map (e => Expressions.instantiateVariables(e, func.formalArgs, args))
  }
  /**
   * The postcondition of this function application (i.e., the postcondition of the function with
   * the arguments instantiated correctly).
   */
  lazy val posts = {
    func.posts map (e => Expressions.instantiateVariables(e, func.formalArgs, args))
  }
}

/** User-defined domain function application. */
case class DomainFuncApp(func: DomainFunc, args: Seq[Exp], typVarMap: Map[TypeVar, Type])(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractDomainFuncApp {
  args foreach Consistency.checkNoPositiveOnly
  override lazy val typ = super.typ.substitute(typVarMap)
  override lazy val formalArgs: Seq[LocalVarDecl] = {
    callee.formalArgs map {
      fa =>
      // substitute parameter types
        LocalVarDecl(fa.name, fa.typ.substitute(typVarMap))(fa.pos)
    }
  }
}

// --- Field and predicate accesses

/** A common trait for expressions accessing a location. */
sealed trait LocationAccess extends Exp {
  def loc: Location
}

object LocationAccess {
  def unapply(la: LocationAccess) = Some(la.loc)
}

/** A field access expression. */
case class FieldAccess(rcv: Exp, field: Field)(val pos: Position = NoPosition, val info: Info = NoInfo) extends LocationAccess with Lhs {
  lazy val loc = field
  lazy val typ = field.typ
}

/** A predicate access expression. */
case class PredicateAccess(args: Seq[Exp], predicate: Predicate)(val pos: Position = NoPosition, val info: Info = NoInfo) extends LocationAccess {
  lazy val loc = predicate
  lazy val typ = Pred

  /** The body of the predicate with the receiver instantiated correctly. */
  lazy val predicateBody =
    Expressions.instantiateVariables(predicate.body, predicate.formalArgs, args)
}

// --- Conditional expression

/** A conditional expressions. */
case class CondExp(cond: Exp, thn: Exp, els: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  require(cond isSubtype Bool)
  Consistency.checkNoPositiveOnly(cond)
  require(thn.typ == els.typ)
  lazy val typ = thn.typ
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
  def variables: Seq[LocalVarDecl]
  def exp: Exp
  lazy val typ = Bool
}
object QuantifiedExp {
  def unapply(q: QuantifiedExp) = Some(q.variables, q.exp)
}

/** Universal quantification. */
case class Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends QuantifiedExp {

  /**
   * Returns an identical forall quantification that has some automatically generated triggers
   * if necessary and possible.
   */
  lazy val autoTrigger: Forall = {
    if (triggers.isEmpty) {
      val gen = Expressions.generateTrigger(this)
      if (gen.size > 0) {
        val (triggers, extraVariables) = gen(0)
        Forall(variables ++ extraVariables, triggers, exp)(pos, info)
      } else {
        // no triggers found
        this
      }
    } else {
      // triggers already present
      this
    }
  }
}

/** Existential quantification. */
case class Exists(variables: Seq[LocalVarDecl], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends QuantifiedExp {
  Consistency.checkNoPositiveOnlyExceptInhaleExhale(exp)
}

/** A trigger for a universally quantified formula. */
case class Trigger(exps: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed {
  require(exps forall Consistency.validTrigger, s"The trigger { ${exps.mkString(", ")} } is not valid.")
  exps foreach Consistency.checkNoPositiveOnly
}

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
case class LocalVar(name: String)(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar with Lhs {
  require(Consistency.validUserDefinedIdentifier(name))
}

/** A special local variable for the result of a function. */
case class Result()(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar {
  lazy val name = "result"
}

// --- Mathematical sequences

/**
 * Marker trait for all sequence-related expressions. Does not imply that the type of the
 * expression is `SeqType`.
 */
sealed trait SeqExp extends Exp

/** The empty sequence of a given element type. */
case class EmptySeq(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  lazy val typ = SeqType(elemTyp)
}

/** An explicit, non-emtpy sequence. */
case class ExplicitSeq(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = SeqType(elems.head.typ)
}

/** A range of integers from 'low' to 'high', not including 'high', but including 'low'. */
case class RangeSeq(low: Exp, high: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require((low isSubtype Int) && (high isSubtype Int))
  lazy val typ = SeqType(Int)
}

/** Appending two sequences of the same type. */
case class SeqAppend(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "++"
  lazy val typ = left.typ
}

/** Access to an element of a sequence at a given index position (starting at 0). */
case class SeqIndex(s: Exp, idx: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(idx isSubtype Int)
  lazy val typ = s.typ.asInstanceOf[SeqType].elementType
}

/** Take the first 'n' elements of the sequence 'seq'. */
case class SeqTake(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(n isSubtype Int)
  lazy val typ = s.typ
}

/** Drop the last 'n' elements of the sequence 'seq'. */
// TODO Is this description really correct? Shouldn't it drop the _first_ n elements?
case class SeqDrop(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(n isSubtype Int)
  lazy val typ = s.typ
}

/** Is the element 'elem' contained in the sequence 'seq'? */
case class SeqContains(elem: Exp, s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp with PrettyBinaryExpression {
  require(s.typ.isInstanceOf[SeqType])
  require(elem isSubtype s.typ.asInstanceOf[SeqType].elementType)
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val left: PrettyExpression = elem
  lazy val op = "in"
  lazy val right: PrettyExpression = s
  lazy val typ = Bool
}

/** The same sequence as 'seq', but with the element at index 'idx' replaced with 'elem'. */
case class SeqUpdate(s: Exp, idx: Exp, elem: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(idx isSubtype Int)
  require(elem isSubtype s.typ.asInstanceOf[SeqType].elementType)
  Consistency.checkNoPositiveOnly(elem)
  lazy val typ = s.typ
}

/** The length of a sequence. */
case class SeqLength(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  lazy val typ = Int
}

// --- Mathematical sets and multisets

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `SetType`.
 */
sealed trait SetExp extends Exp

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `MultisetType`.
 */
sealed trait MultisetExp extends Exp

/** The empty set of a given element type. */
case class EmptySet(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp {
  lazy val typ = SetType(elemTyp)
}

/** An explicit, non-empty set. */
case class ExplicitSet(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = SetType(elems.head.typ)
}

/** The empty multiset of a given element type. */
case class EmptyMultiset(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends MultisetExp {
  lazy val typ = MultisetType(elemTyp)
}

/** An explicit, non-empty multiset. */
case class ExplicitMultiset(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends MultisetExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = MultisetType(elems.head.typ)
}

/** Union of two sets or two multisets. */
case class AnySetUnion(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "union"
  lazy val typ = left.typ
}

/** Intersection of two sets or two multisets. */
case class AnySetIntersection(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "union"
  lazy val typ = left.typ
}

/** Subset relation of two sets or two multisets. */
case class AnySetSubset(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val op = "subset"
  lazy val typ = Bool
}

/** Set difference. */
case class AnySetMinus(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val op = "setminus"
  lazy val typ = left.typ
}

/** Is the element 'elem' contained in the sequence 'seq'? */
case class AnySetContains(elem: Exp, s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp with PrettyBinaryExpression {
  require((s.typ.isInstanceOf[SetType] && (elem isSubtype s.typ.asInstanceOf[SetType].elementType)) ||
    (s.typ.isInstanceOf[MultisetType] && (elem isSubtype s.typ.asInstanceOf[MultisetType].elementType)))
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val left: PrettyExpression = elem
  lazy val op = "in"
  lazy val right: PrettyExpression = s
  lazy val typ = Bool
}

/** The length of a sequence. */
case class AnySetCardinality(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp with MultisetExp {
  require(s.typ.isInstanceOf[SetType] || s.typ.isInstanceOf[MultisetType])
  lazy val typ = Int
}

// --- Common functionality

/** Common super trait for all kinds of literals. */
sealed trait Literal extends Exp

/**
 * A common class for concrete permissions.  The name AbstractConcretePerm is used because it is an abstract superclass for concrete permissions.
 */
sealed abstract class AbstractConcretePerm(val numerator: BigInt, val denominator: BigInt) extends PermExp

/** Common ancestor of Domain Function applications and Function applications. */
sealed trait FuncLikeApp extends Exp with Call {
  def func: FuncLike
  lazy val callee = func
  def typ = func.typ
}
object FuncLikeApp {
  def unapply(fa: FuncLikeApp) = Some((fa.func, fa.args))
  def apply(f: FuncLike, args: Seq[Exp], typVars: Map[TypeVar, Type]) = {
    f match {
      case f@Function(_, _, _, _, _, _) => FuncApp(f, args)()
      case f@DomainFunc(_, _, _, _) => DomainFuncApp(f, args, typVars)()
      case _ => sys.error(s"should not occur: $f (${f.getClass})")
    }
  }
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
  require(left.typ == right.typ, s"expected the same typ, but got ${left.typ} and ${right.typ}")
  Consistency.checkNoPositiveOnly(left)
  Consistency.checkNoPositiveOnly(right)
  lazy val priority = 13
  lazy val fixity = Infix(NonAssoc)
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
object DomainBinExp {
  def unapply(e: DomainBinExp) = Some((e.left, e.func, e.right))
}

/** Common superclass for unary expressions that belong to a domain (and thus have a domain operator). */
sealed abstract class DomainUnExp(val func: UnOp) extends PrettyUnaryExpression with DomainOpExp with UnExp

/** Expressions which can appear on the left hand side of an assignment */
sealed trait Lhs extends Exp
