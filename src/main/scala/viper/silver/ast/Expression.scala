/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

import org.kiama.output._
import utility.{GenericTriggerGenerator, Expressions, Consistency}

/** Expressions. */
sealed trait Exp extends Node with Typed with Positioned with Infoed with PrettyExpression {

  lazy val isPure = Expressions.isPure(this)
  def isHeapDependent(p: Program) = Expressions.isHeapDependent(this, p)

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

  // AS: experimenting with removing this code...
  /**
   * Returns a conjunction of all proof obligations in this expression, e.g. rcv != null for all field accesses rcv.f,
   * we have permissions for all field accesses, the preconditions of all used functions are fulfilled etc.
   */
 // lazy val proofObligations = Expressions.proofObligations(this)

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

/** Integer unary minus. */
case class Minus(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainUnExp(NegOp)

// Boolean expressions
case class Or(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(OrOp) {
  Consistency.checkNoPositiveOnly(left)
  Consistency.checkNoPositiveOnly(right)
}
case class And(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(AndOp)
case class Implies(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(ImpliesOp) {
  Consistency.checkNoPositiveOnly(left)
}

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
{
  require(left.typ==Int)
  require(right.typ==Int)
}

case class PermDiv(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainBinExp(PermDivOp) with PermExp
{
  require(left.typ==Perm)
  require(right.typ==Int)
}
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
case class FuncApp(funcname: String, args: Seq[Exp])(val pos: Position, val info: Info, override val typ : Type, override val formalArgs: Seq[LocalVarDecl]) extends FuncLikeApp with PossibleTrigger {
  args foreach Consistency.checkNoPositiveOnly
//  args foreach (_.isPure)

  def func : (Program => Function) = (p) => p.findFunction(funcname)
  def getArgs = args
  def withArgs(newArgs: Seq[Exp]) = FuncApp(funcname, newArgs)(pos,info,typ,formalArgs)
  def asManifestation = this
}
// allows a FuncApp to be created directly from a Function node (but only stores its name)
object FuncApp {
  def apply(func: Function, args: Seq[Exp])(pos: Position = NoPosition, info: Info = NoInfo) : FuncApp = FuncApp(func.name, args)(pos,info,func.typ,func.formalArgs)
}

/** User-defined domain function application. */
case class DomainFuncApp(funcname: String, args: Seq[Exp], typVarMap: Map[TypeVar, Type])(val pos: Position, val info: Info, typPassed: => Type, formalArgsPassed: => Seq[LocalVarDecl]) extends AbstractDomainFuncApp with PossibleTrigger {
  args foreach Consistency.checkNoPositiveOnly
//  args foreach (_.isPure)
  def typ = typPassed
  def formalArgs = formalArgsPassed
  def func = (p:Program) => p.findDomainFunction(funcname)
  def getArgs = args
  def withArgs(newArgs: Seq[Exp]) = DomainFuncApp(funcname,newArgs,typVarMap)(pos,info,typ,formalArgs)
  def asManifestation = this
}
object DomainFuncApp {
  def apply(func : DomainFunc, args: Seq[Exp], typVarMap: Map[TypeVar, Type])(pos: Position = NoPosition, info: Info = NoInfo) : DomainFuncApp = DomainFuncApp(func.name,args,typVarMap)(pos,info,func.typ.substitute(typVarMap),func.formalArgs map {
    fa =>
      // substitute parameter types
      LocalVarDecl(fa.name, fa.typ.substitute(typVarMap))(fa.pos)
  })
}

// --- Field and predicate accesses

/** A common trait for expressions accessing a location. */
sealed trait LocationAccess extends Exp {
  def loc(p : Program): Location
}

object LocationAccess {
  def unapply(la: LocationAccess) = Some((p:Program) => la.loc(p))
}


/** A field access expression. */
case class FieldAccess(rcv: Exp, field: Field)(val pos: Position = NoPosition, val info: Info = NoInfo) extends LocationAccess with Lhs {
  def loc(p : Program) = field
  lazy val typ = field.typ
}

/** A predicate access expression. See also companion object below for an alternative creation signature */
case class PredicateAccess(args: Seq[Exp], predicateName: String)(val pos: Position, val info: Info) extends LocationAccess {
  def loc(p:Program) = p.findPredicate(predicateName)
  lazy val typ = Pred

  /** The body of the predicate with the arguments instantiated correctly. */
  def predicateBody(program : Program) = {
    val predicate = program.findPredicate(predicateName)
    predicate.body map (Expressions.instantiateVariables(_, predicate.formalArgs, args))
  }
}
// allows PredicateAccess to be created from a predicate directly, in which case only the name is kept
object PredicateAccess {
  def apply(args: Seq[Exp], predicate:Predicate)(pos: Position = NoPosition, info: Info = NoInfo) : PredicateAccess = PredicateAccess(args, predicate.name)(pos, info)
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
  Consistency.checkNoPositiveOnlyExceptInhaleExhale(exp)

  lazy val typ = exp.typ
}

// --- Old expression

case class Old(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends UnExp {
  Consistency.checkNoPositiveOnly(exp)
  //require(exp.isPure)
  lazy val typ = exp.typ
}

// --- Other expressions

case class Let(variable: LocalVarDecl, exp: Exp, body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Exp {
  require(exp.typ isSubtype variable.typ,
          s"Let-bound variable ${variable.name} is of type ${variable.typ}, but bound expression is of type ${exp.typ}")

  val typ = body.typ
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
        gen.find(pair => pair._2.isEmpty) match {
          case Some((newTriggers, _)) => Forall(variables, newTriggers, exp)(pos,info)
          case None =>
            val (triggers, extraVariables) = gen(0) // somewhat arbitrarily take the first choice
            Forall(variables ++ extraVariables, triggers, exp)(pos, info)
        }
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

/* TODO: [2015-01-24 Malte]
 *       Why are pos and info part of the first argument list of the constructors of
 *       LocalVar and Result? In all (?) other cases, they are part of the second
 *       list of arguments.
 *       Note: Changing this likely break all tools that (de)construct Silver ASTs.
 *       The entailed changes should be trivial to make, though.
 */

/** A normal local variable. */
case class LocalVar(name: String)(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractLocalVar with Lhs {
  require(Consistency.validUserDefinedIdentifier(name))
  require(typ != null)
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
sealed trait SeqExp extends Exp with PossibleTrigger {
  override def asManifestation = this
}

/** The empty sequence of a given element type. */
case class EmptySeq(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  lazy val typ = SeqType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this
}

/** An explicit, non-empty sequence. */
case class ExplicitSeq(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = SeqType(elems.head.typ)
  lazy val desugared : SeqExp = {
    elems match {
      case Nil => sys.error("did not expect empty sequence")
      case a :: Nil => this
      case a :: as => // desugar into singleton sequences and appends
        as.foldLeft[SeqExp](ExplicitSeq(Seq(a))(pos,info)) {
          (bs:SeqExp, b:Exp) => SeqAppend(bs,ExplicitSeq(Seq(b))(pos,info))(pos, info)
        }
    }
  }
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitSeq(newArgs)(pos,info)
}

/** A range of integers from 'low' to 'high', not including 'high', but including 'low'. */
case class RangeSeq(low: Exp, high: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require((low isSubtype Int) && (high isSubtype Int))
  lazy val typ = SeqType(Int)
  def getArgs = Seq(low,high)
  def withArgs(newArgs: Seq[Exp]) = RangeSeq(newArgs(0),newArgs(1))(pos,info)
}

/** Appending two sequences of the same type. */
case class SeqAppend(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp with PrettyBinaryExpression {
  require(left.typ == right.typ)
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "++"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = SeqAppend(newArgs(0),newArgs(1))(pos,info)

}

/** Access to an element of a sequence at a given index position (starting at 0). */
case class SeqIndex(s: Exp, idx: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(idx isSubtype Int)
  lazy val typ = s.typ.asInstanceOf[SeqType].elementType
  def getArgs = Seq(s,idx)
  def withArgs(newArgs: Seq[Exp]) = SeqIndex(newArgs(0),newArgs(1))(pos,info)
}

/** Take the first 'n' elements of the sequence 'seq'. */
case class SeqTake(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(n isSubtype Int)
  lazy val typ = s.typ
  def getArgs = Seq(s,n)
  def withArgs(newArgs: Seq[Exp]) = SeqTake(newArgs(0),newArgs(1))(pos,info)

}

/** Drop the first 'n' elements of the sequence 'seq'. */
case class SeqDrop(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(n isSubtype Int)
  lazy val typ = s.typ
  def getArgs = Seq(s,n)
  def withArgs(newArgs: Seq[Exp]) = SeqDrop(newArgs(0),newArgs(1))(pos,info)

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
  def getArgs = Seq(elem,s)
  def withArgs(newArgs: Seq[Exp]) = SeqContains(newArgs(0),newArgs(1))(pos,info)
}

/** The same sequence as 'seq', but with the element at index 'idx' replaced with 'elem'. */
case class SeqUpdate(s: Exp, idx: Exp, elem: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  require(idx isSubtype Int)
  require(elem isSubtype s.typ.asInstanceOf[SeqType].elementType)
  Consistency.checkNoPositiveOnly(elem)
  lazy val typ = s.typ
  def getArgs = Seq(s,idx,elem)
  def withArgs(newArgs: Seq[Exp]) = SeqUpdate(newArgs(0),newArgs(1),newArgs(2))(pos,info)

}

/** The length of a sequence. */
case class SeqLength(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SeqExp {
  require(s.typ.isInstanceOf[SeqType])
  lazy val typ = Int
  def getArgs = Seq(s)
  def withArgs(newArgs: Seq[Exp]) = SeqLength(newArgs(0))(pos,info)

}

// --- Mathematical sets and multisets

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `SetType`.
 */
sealed trait SetExp extends Exp with PossibleTrigger {
  override def asManifestation:Exp = this
}

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `MultisetType`.
 */
sealed trait MultisetExp extends Exp with PossibleTrigger {
  override def asManifestation:Exp = this
}

/**
 * Marker traits for all expressions that correspond to operations on sets or multisets.
 * Does not imply that the type of the expression is `SetType` or `MultisetType`.
 */
sealed trait AnySetExp extends SetExp with MultisetExp
sealed trait AnySetUnExp extends AnySetExp with UnExp
sealed trait AnySetBinExp extends AnySetExp with PrettyBinaryExpression with BinExp

/** The empty set of a given element type. */
case class EmptySet(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp {
  lazy val typ = SetType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this
}

/** An explicit, non-empty set. */
case class ExplicitSet(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends SetExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = SetType(elems.head.typ)
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitSet(newArgs)(pos,info)

}

/** The empty multiset of a given element type. */
case class EmptyMultiset(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends MultisetExp {
  lazy val typ = MultisetType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this

}

/** An explicit, non-empty multiset. */
case class ExplicitMultiset(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends MultisetExp {
  require(elems.length > 0)
  require(elems.tail.forall(e => e.typ == elems.head.typ))
  elems foreach Consistency.checkNoPositiveOnly
  lazy val typ = MultisetType(elems.head.typ)
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitMultiset(newArgs)(pos,info)

}

/** Union of two sets or two multisets. */
case class AnySetUnion(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetBinExp {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "union"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetUnion(newArgs(0),newArgs(1))(pos,info)
}

/** Intersection of two sets or two multisets. */
case class AnySetIntersection(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetBinExp {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(LeftAssoc)
  lazy val op = "union"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetIntersection(newArgs(0),newArgs(1))(pos,info)
}

/** Subset relation of two sets or two multisets. */
case class AnySetSubset(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetBinExp {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val op = "subset"
  lazy val typ = Bool
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetSubset(newArgs(0),newArgs(1))(pos,info)
}

/** Set difference. */
case class AnySetMinus(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetBinExp {
  require(left.typ == right.typ)
  require(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val op = "setminus"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetMinus(newArgs(0),newArgs(1))(pos,info)
}

/** Is the element 'elem' contained in the sequence 'seq'? */
case class AnySetContains(elem: Exp, s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetBinExp {
  require((s.typ.isInstanceOf[SetType] && (elem isSubtype s.typ.asInstanceOf[SetType].elementType)) ||
    (s.typ.isInstanceOf[MultisetType] && (elem isSubtype s.typ.asInstanceOf[MultisetType].elementType)))
  lazy val priority = 0
  lazy val fixity = Infix(NonAssoc)
  lazy val left = elem
  lazy val op = "in"
  lazy val right = s
  lazy val typ = Bool
  def getArgs = Seq(elem,s)
  def withArgs(newArgs: Seq[Exp]) = AnySetContains(newArgs(0),newArgs(1))(pos,info)
}

/** The length of a sequence. */
case class AnySetCardinality(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AnySetUnExp {
  require(s.typ.isInstanceOf[SetType] || s.typ.isInstanceOf[MultisetType])
  val exp = s
  lazy val typ = Int
  def getArgs = Seq(s)
  def withArgs(newArgs: Seq[Exp]) = AnySetCardinality(newArgs(0))(pos,info)
}

// --- Common functionality

/** Common super trait for all kinds of literals. */
sealed trait Literal extends Exp

/**
 * A common class for concrete permissions.  The name AbstractConcretePerm is used because it is an abstract superclass for concrete permissions.
 */
sealed abstract class AbstractConcretePerm(val numerator: BigInt, val denominator: BigInt) extends PermExp

/**
 * Used to label expression nodes as potentially valid trigger terms for quantifiers.
 * Use ForbiddenInTrigger to declare terms which may not be used in triggers.
 */
sealed trait PossibleTrigger extends GenericTriggerGenerator.PossibleTrigger[Exp, PossibleTrigger] {
  def pos : Position
  def info : Info
}

sealed trait WrappingTrigger extends PossibleTrigger
    with GenericTriggerGenerator.WrappingTrigger[Exp, PossibleTrigger, WrappingTrigger]

// Representation for a trigger term to be evaluated in the "old" heap
case class OldTrigger(wrappee: PossibleTrigger)(val pos: Position = NoPosition, val info: Info = NoInfo)
    extends WrappingTrigger {

  def getArgs = wrappee.getArgs
  def withArgs(args : Seq[Exp]) = OldTrigger(wrappee.withArgs(args))(pos,info)
  def asManifestation = Old(wrappee.asManifestation)(pos,info)
}
object OldTrigger { // creates an instance, recording the pos and info of the old expression
  def apply(oldExp : Old) : OldTrigger = {
    val exp = oldExp.exp match {
      case trigger: PossibleTrigger => trigger
      case _ => sys.error("Internal Error: tried to create invalid trigger node from : " + oldExp)
    }

    OldTrigger(exp)(oldExp.pos, oldExp.info)
  }
}

sealed trait ForbiddenInTrigger extends Exp with GenericTriggerGenerator.ForbiddenInTrigger[Type]

/** Common ancestor of Domain Function applications and Function applications. */
sealed trait FuncLikeApp extends Exp with Call {
  def func: Program => FuncLike
  def callee = funcname
  def funcname: String
}
object FuncLikeApp {
  def unapply(fa: FuncLikeApp) = Some((fa.funcname, fa.args))
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
  def func: Program => AbstractDomainFunc
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
sealed trait DomainOpExp extends AbstractDomainFuncApp with ForbiddenInTrigger { // ForbiddenInTrigger: seems likely that all such operators will not be allowed if/when translated to Z3. But if we need something more fine-grained, we can push this further down the hierarchy.
  def func: Program => Op
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
sealed abstract class DomainBinExp(val funct: BinOp) extends BinExp with DomainOpExp
{
  def func = (p:Program) => funct
  def funcname = funct.name
  def formalArgs = funct.formalArgs
  def op = funct.op
  def fixity = funct.fixity
  def priority = funct.priority
  def typ = funct.typ
}
object DomainBinExp {
  def unapply(e: DomainBinExp) = Some((e.left, e.funct, e.right))
}

/** Common superclass for unary expressions that belong to a domain (and thus have a domain operator). */
sealed abstract class DomainUnExp(val funct: UnOp) extends PrettyUnaryExpression with DomainOpExp with UnExp {
  def func = (p:Program) => funct
  def funcname = funct.name
  def typ = funct.typ
  def formalArgs = funct.formalArgs
  def op = funct.op
  def fixity = funct.fixity
  def priority = funct.priority
}

/** Expressions which can appear on the left hand side of an assignment */
sealed trait Lhs extends Exp
