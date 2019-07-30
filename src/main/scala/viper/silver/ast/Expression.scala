// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import viper.silver.ast.MagicWandStructure.MagicWandStructure
import viper.silver.ast.pretty._
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.ast.utility._
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.parser.FastParser
import viper.silver.verifier.{ConsistencyError, VerificationResult}

/** Expressions. */
sealed trait Exp extends Hashable with Typed with Positioned with Infoed with TransformableErrors with PrettyExpression {
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

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  /** @inheritdoc */
  lazy val topLevelConjuncts = Expressions.topLevelConjuncts(this)

  // AS: experimenting with removing this code...
  /**
   * Returns a conjunction of all proof obligations in this expression, e.g. rcv != null for all field accesses rcv.f,
   * we have permissions for all field accesses, the preconditions of all used functions are fulfilled etc.
   */
 // lazy val proofObligations = Expressions.proofObligations(this)

}

// --- Simple integer and boolean expressions (binary and unary operations, literals)

// Arithmetic expressions
case class Add(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(AddOp) with ForbiddenInTrigger
case class Sub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(SubOp) with ForbiddenInTrigger
case class Mul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(MulOp) with ForbiddenInTrigger
case class Div(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(DivOp) with ForbiddenInTrigger
case class Mod(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(ModOp) with ForbiddenInTrigger

// Integer comparison expressions
case class LtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(LtOp) with ForbiddenInTrigger
case class LeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(LeOp) with ForbiddenInTrigger
case class GtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(GtOp) with ForbiddenInTrigger
case class GeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(GeOp) with ForbiddenInTrigger

// Equality and non-equality (defined for all types)
case class EqCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends EqualityCmp("==") {
  override lazy val check : Seq[ConsistencyError] =
    Seq(left, right).flatMap(Consistency.checkPure) ++
    (if(left.typ != right.typ) Seq(ConsistencyError(s"expected the same type, but got ${left.typ} and ${right.typ}", left.pos)) else Seq())
}
case class NeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends EqualityCmp("!=") {
  override lazy val check : Seq[ConsistencyError] =
    Seq(left, right).flatMap(Consistency.checkPure) ++
    (if(left.typ != right.typ) Seq(ConsistencyError(s"expected the same type, but got ${left.typ} and ${right.typ}", left.pos)) else Seq())
}

/** Integer literal. */
case class IntLit(i: BigInt)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Literal {
  lazy val typ = Int
}

/** Integer unary minus. */
case class Minus(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainUnExp(NegOp)

// Boolean expressions
case class Or(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(OrOp) with ForbiddenInTrigger {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(left) ++ Consistency.checkPure(right)
}

case class And(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(AndOp) with ForbiddenInTrigger

case class Implies(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(ImpliesOp) with ForbiddenInTrigger {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(left)
}

object MagicWandStructure {
  type MagicWandStructure = MagicWand
}

case class MagicWand(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
    extends DomainBinExp(MagicWandOp)
       with Resource
       with ResourceAccess
       with AccessPredicate {

  /* [2018-10-08 Malte] Magic wands are currently not wrapped in acc(...); to account for that,
   * a `MagicWand` is currently both a `ResourceAccess` and an `AccessPredicate`.
   * It is also a `Resource` because we do not declare wands separately from wand instances, in
   * contrast to e.g. fields and predicates.
   */

  override def res(p: Program): Resource = this
  def loc: ResourceAccess = this
  val perm: Exp = FullPerm()(pos, NoInfo, NoTrafos)

  override val typ: Wand.type = Wand

  // maybe rename this sometime
  def subexpressionsToEvaluate(p: Program): Seq[Exp] = {
    /* The code collects expressions that can/are to be evaluated in a fixed state, i.e.
     * a state that is known when this method is called.
     * Among other things, such expressions may not be heap-dependent (unless they are nested
     * under old-expressions) and they may not contain bound (e.g. quantified) variables.
     *
     * I [Malte] tried using our new AST transformation framework, in particular a Visitor and a
     * Query, but the former doesn't return anything (it could be executed for its side-effect,
     * though) and the latter doesn't take a context. We should change that.
     */

    var collectedExpressions = Vector.empty[Exp]

    def go(root: Exp, boundVariables: Set[LocalVar]): Unit = {
      root.visitWithContextManually(boundVariables)(boundVariables => {
        case LabelledOld(_, FastParser.LHS_OLD_LABEL) => /* Don't descend further */

        case Let(v, e, body) => go(body.replace(v.localVar, e), boundVariables)

        case old: OldExp if !boundVariables.exists(old.contains)=>
          collectedExpressions :+= old

        case quant: QuantifiedExp =>
          val newContext = boundVariables ++ quant.variables.map(_.localVar)

          quant.children.collect { case e: Exp => e } .foreach(go(_, newContext))

        case e: Exp if !e.isHeapDependent(p) && !boundVariables.exists(e.contains) =>
          collectedExpressions :+= e
      })
    }

    go(this, Set.empty)

    collectedExpressions
  }

  def structure(p: Program): MagicWandStructure = {
    /* High-level idea: take the input wand (`this`) and perform a sequence of
     * substitutions that transform the wand into a canonical form suitable for
     * checking whether or not a given state provides a particular wand.
     *
     * The substitutions are:
     *   - Replace holes in the wand (subexpressions to evaluate) by local variables
     *     whose names are the type of the hole. E.g. "n + 1" is replaced by an
     *     artificial variable with name "int" and similarly, "n < m" by "bool".
     *   - Quantified variables are given canonical names based on their depth/level
     *     of nesting in the overall wand. E.g. the subexpression
     *     "(forall x, y :: b1(x, y) ==> forall z :: b2(x, y, z)) && forall x :: b3(x)"
     *     is transformed into
     *     "(forall q1, q2 :: b1(q1, q2) ==> forall q3 :: b2(q1, q2, q3)) && forall q1 :: b3(q1)".
     *
     * Wands transformed in this way can be compared for equality as follows: an initial
     * syntactic comparison can be used to check if the wands match structurally, a subsequent
     * semantic comparison of their arguments (the values that go into the wands' holes) then
     * ensures that the wands are actually (i.e. semantically) equivalent.
     */

    val subexpressionsToEvaluate = this.subexpressionsToEvaluate(p)

    type Bindings = Map[String, Int]
    val Bindings = Map

    def name(typ: Type, index: Int): String = s"${typ}_$index"

    def extendBindings(bindings: Bindings, extension: Seq[LocalVarDecl]): Bindings = {
      var count = bindings.size

      val additionalBindings =
        extension.map(decl => {
          count += 1

          decl.name -> count
        })

      bindings ++ additionalBindings
    }

    def renameDecls(decls: Seq[LocalVarDecl], bindings: Bindings): Seq[LocalVarDecl] = {
      decls.map(decl =>
        decl.copy(name(decl.typ, bindings(decl.name)))(decl.pos, decl.info, decl.errT))
    }

    StrategyBuilder.Context[Node, Bindings](
      {
        case (exp: Exp, _) if subexpressionsToEvaluate.contains(exp) =>
          LocalVar(exp.typ.toString(),exp.typ)()

        case (quant: QuantifiedExp, context) =>
          /* NOTE: This case, i.e. the transformation case, is reached before the
           *       corresponding case in the context update function (defined below)
           *       is reached. This unfortunately means that we have to duplicate work,
           *       i.e. we have to compute the new bindings twice.
           */
          val bindings = extendBindings(context.c, quant.variables)
          val variables = renameDecls(quant.variables, bindings)

          quant.withVariables(variables)

        case (lv: LocalVar, context) =>
          context.c.get(lv.name) match {
            case None => lv
            case Some(index) => lv.copy(name(lv.typ, index), lv.typ)(lv.pos, lv.info, lv.errT)
          }
      },
      Bindings.empty,
      { case (quant: QuantifiedExp, bindings) => extendBindings(bindings, quant.variables) },
      Traverse.TopDown
    ).execute[this.type](this)
  }

  override def isValid : Boolean = this match {
    case _ if  left.contains[ForPerm] => false
    case _ if right.contains[ForPerm] => false
    case _ if  left.deepCollect{ case q: Forall if !q.isPure => q }.nonEmpty => false
    case _ if right.deepCollect{ case q: Forall if !q.isPure => q }.nonEmpty => false
    case _ => true
  }
}

/** Boolean negation. */
case class Not(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainUnExp(NotOp) {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(exp)
}

/** Boolean literals. */
sealed abstract class BoolLit(val value: Boolean) extends Literal {
  lazy val typ = Bool
}
object BoolLit {
  def unapply(b: BoolLit) = Some(b.value)
  def apply(b: Boolean)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) = if (b) TrueLit()(pos, info, errT) else FalseLit()(pos, info, errT)
}
case class TrueLit()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends BoolLit(true)
case class FalseLit()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends BoolLit(false)

case class NullLit()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Literal {
  lazy val typ = Ref
}

// --- Accessibility predicates

/** A common trait for accessibility predicates. */
// Note: adding extra instances of AccessPredicate will require adding cases to viper.silver.ast.utility.multiplyExpByPerm method
sealed trait AccessPredicate extends Exp {
  def res(p: Program): Resource = loc.res(p)
  def loc: ResourceAccess /* TODO: Should be renamed to, e.g. `resAcc` or just `acc` */
  def perm: Exp
}
object AccessPredicate {
  def unapply(a: AccessPredicate) = Some((a.loc, a.perm))
}

/** An accessibility predicate for a field location. */
case class FieldAccessPredicate(loc: FieldAccess, perm: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AccessPredicate {
  override lazy val check : Seq[ConsistencyError] =
    if(!(perm isSubtype Perm)) Seq(ConsistencyError(s"Permission amount parameter of access predicate must be of Perm type, but found ${perm.typ}", perm.pos)) else Seq()
  val typ: Bool.type = Bool
}

/** An accessibility predicate for a predicate location. */
case class PredicateAccessPredicate(loc: PredicateAccess, perm: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AccessPredicate {
  override lazy val check : Seq[ConsistencyError] =
    if(!(perm isSubtype Perm)) Seq(ConsistencyError(s"Permission amount parameter of access predicate must be of Perm type, but found ${perm.typ}", perm.pos)) else Seq()
  val typ: Bool.type = Bool
}

// --- Inhale exhale expressions.

/**
 * This is a special expression that is treated as `in` if it appears as an assumption and as `ex` if
 * it appears as a proof obligation.
 */
case class InhaleExhaleExp(in: Exp, ex: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Exp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!(in.typ isSubtype Bool)) Seq(ConsistencyError(s"First parameter to inhale-exhale assertion must be of Bool type, but found ${in.typ}", in.pos)) else Seq()) ++
    (if(!(ex.typ isSubtype Bool)) Seq(ConsistencyError(s"Second parameter to inhale-exhale assertion must be of Bool type, but found ${ex.typ}", ex.pos)) else Seq())
  val typ = Bool
}

// --- Permissions

/** A common trait for expressions of type permission. */
sealed trait PermExp extends Exp {
  override lazy val typ = Perm
}

/** A wild card permission. Has an unknown value, but there are no guarantees that it will be the same inside one method. */
case class WildcardPerm()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends PermExp

/** The full permission. */
case class FullPerm()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractConcretePerm(1, 1)

/** No permission. */
case class NoPerm()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractConcretePerm(0, 1)

/** An epsilon permission. */
case class EpsilonPerm()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends PermExp

/** A concrete fraction as permission amount. */
case class FractionalPerm(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(FracOp) with PermExp with ForbiddenInTrigger
{
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != Int) Seq(ConsistencyError(s"Numerator type of fractional permission must be Int, but found ${left.typ}", left.pos)) else Seq()) ++
    (if(right.typ != Int) Seq(ConsistencyError(s"Denominator type of fractional permission must be Int, but found ${right.typ}", right.pos)) else Seq())
}

case class PermDiv(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermDivOp) with PermExp with ForbiddenInTrigger
{
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != Perm) Seq(ConsistencyError(s"First parameter of permission division expression must be Perm, but found ${left.typ}", left.pos)) else Seq()) ++
    (if(right.typ != Int) Seq(ConsistencyError(s"Second parameter of permission division expression must be Int, but found ${right.typ}", right.pos)) else Seq())
}
/** The permission currently held for a given resource. */
case class CurrentPerm(res: ResourceAccess)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends PermExp

// Arithmetic expressions
case class PermMinus(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainUnExp(PermNegOp) with PermExp
case class PermAdd(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermAddOp) with PermExp with ForbiddenInTrigger
case class PermSub(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermSubOp) with PermExp with ForbiddenInTrigger
case class PermMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermMulOp) with PermExp with ForbiddenInTrigger
case class IntPermMul(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(IntPermMulOp) with PermExp with ForbiddenInTrigger

// Comparison expressions
case class PermLtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermLtOp) with ForbiddenInTrigger
case class PermLeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermLeOp) with ForbiddenInTrigger
case class PermGtCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermGtOp) with ForbiddenInTrigger
case class PermGeCmp(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends DomainBinExp(PermGeOp) with ForbiddenInTrigger

// --- Function application (domain and normal)

/** Function application. */
case class FuncApp(funcname: String, args: Seq[Exp])(val pos: Position, val info: Info, override val typ : Type, val errT: ErrorTrafo) extends FuncLikeApp with PossibleTrigger {
  override lazy val check : Seq[ConsistencyError] = args.flatMap(Consistency.checkPure)

  def func : (Program => Function) = (p) => p.findFunction(funcname)
  def getArgs = args
  def withArgs(newArgs: Seq[Exp]) = FuncApp(funcname, newArgs)(pos, info, typ, errT)
  def asManifestation = this
}
// allows a FuncApp to be created directly from a Function node (but only stores its name)
object FuncApp {
  def apply(func: Function, args: Seq[Exp])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) : FuncApp = FuncApp(func.name, args)(pos, info, func.typ, errT)
}

/** User-defined domain function application. */
case class DomainFuncApp(funcname: String, args: Seq[Exp], typVarMap: Map[TypeVar, Type])
                        (val pos: Position, val info: Info, typPassed: => Type, val domainName:String, val errT: ErrorTrafo)
  extends AbstractDomainFuncApp with PossibleTrigger {
  override lazy val check : Seq[ConsistencyError] = args.flatMap(Consistency.checkPure)

  def typ = typPassed
  def func = (p:Program) => p.findDomainFunction(funcname)
  def getArgs = args
  def withArgs(newArgs: Seq[Exp]) = DomainFuncApp(funcname,newArgs,typVarMap)(pos,info,typ,domainName, errT)
  def asManifestation = this

  //Strangely, the copy method is not a member of the DomainFuncApp case class,
  //therefore, We need this method that does the copying manually
  def copy(funcname: String = this.funcname, args: Seq[Exp] = this.args, typVarMap: Map[TypeVar, Type] = this.typVarMap): (Position, Info, => Type, String, ErrorTrafo) => DomainFuncApp ={
    DomainFuncApp(this.funcname,args,typVarMap)
  }
}
object DomainFuncApp {
  def apply(func : DomainFunc, args: Seq[Exp], typVarMap: Map[TypeVar, Type])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) : DomainFuncApp =
    DomainFuncApp(func.name,args,typVarMap)(pos, info, func.typ.substitute(typVarMap), func.domainName, errT)
}

// --- Field and predicate accesses

/** A common trait for expressions accessing a location. */
sealed trait LocationAccess extends Exp with ResourceAccess {
  def loc(p : Program): Location
  override def res(p: Program): Resource = loc(p)
}

sealed trait ResourceAccess extends Exp {
  def res(p: Program): Resource
}

object LocationAccess {
  def unapply(la: LocationAccess) = Some((p:Program) => la.loc(p))
}


/** A field access expression. */
case class FieldAccess(rcv: Exp, field: Field)
                      (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
    extends LocationAccess with Lhs /* with PossibleTrigger */ {

  def loc(p : Program) = field
  lazy val typ = field.typ

  def getArgs: Seq[Exp] = Seq(rcv)
  def withArgs(args: Seq[Exp]): FieldAccess = copy(rcv = args.head, field)(pos, info, errT)
//  def asManifestation: Exp = this
}

/** A predicate access expression. See also companion object below for an alternative creation signature */
case class PredicateAccess(args: Seq[Exp], predicateName: String)
                          (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
    extends LocationAccess {

  def loc(p:Program) = p.findPredicate(predicateName)
  lazy val typ = Bool

  /** The body of the predicate with the arguments instantiated correctly. */
  def predicateBody(program : Program) = {
    val predicate = program.findPredicate(predicateName)
    predicate.body map (Expressions.instantiateVariables(_, predicate.formalArgs, args))
  }
}

// allows PredicateAccess to be created from a predicate directly, in which case only the name is kept
object PredicateAccess {
  def apply(args: Seq[Exp], predicate:Predicate)(pos: Position, info: Info, errT: ErrorTrafo): PredicateAccess = PredicateAccess(args, predicate.name)(pos, info, errT)
}

// --- Conditional expression

/** A conditional expressions. */
case class CondExp(cond: Exp, thn: Exp, els: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
    extends Exp with ForbiddenInTrigger {

  override lazy val check : Seq[ConsistencyError] =
    (if(!(cond isSubtype Bool)) Seq(ConsistencyError(s"Condition must be of Bool type, but found ${cond.typ}", cond.pos)) else Seq()) ++
    Consistency.checkPure(cond) ++
    (if(thn.typ != els.typ) Seq(ConsistencyError(s"Second and third parameter types of conditional expression must match, but found ${thn.typ} and ${els.typ}", thn.pos)) else Seq())

  lazy val typ = thn.typ
}

// --- Prover hint expressions

case class Unfolding(acc: PredicateAccessPredicate, body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Exp {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(body)
  lazy val typ = body.typ
}

case class Applying(wand: MagicWand, body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Exp {
  override lazy val check : Seq[ConsistencyError] = (if(!(wand isSubtype Wand)) Seq(ConsistencyError(s"Expected wand but found ${wand.typ} ($wand)", wand.pos)) else Seq()) ++ Consistency.checkPure(body)
  lazy val typ = body.typ
}

// --- Old expressions

sealed trait OldExp extends UnExp {
  lazy val typ = exp.typ
}

case class Old(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends OldExp {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(exp)
}

/** Old expression that references a particular state earlier in the program that has been given a name.
  * Evaluates expression in that state. */
case class LabelledOld(exp: Exp, oldLabel: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends OldExp {
  override lazy val check : Seq[ConsistencyError] =
      Consistency.checkPure(exp)
}

// --- Other expressions

case class Let(variable: LocalVarDecl, exp: Exp, body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Exp with Scope {
  override lazy val check : Seq[ConsistencyError] =
    if(!(exp.typ isSubtype variable.typ)) Seq(ConsistencyError( s"Let-bound variable ${variable.name} is of type ${variable.typ}, but bound expression is of type ${exp.typ}", exp.pos)) else Seq()
  val typ = body.typ
  val scopedDecls: Seq[Declaration] = Seq(variable)
}

// --- Quantifications

/** A common trait for quantified expressions. */
sealed trait QuantifiedExp extends Exp with Scope {
  def variables: Seq[LocalVarDecl]
  def exp: Exp
  lazy val typ = Bool
  val scopedDecls: Seq[Declaration] = variables

  override def isValid : Boolean = this match {
    case _ if contains[MagicWand] => false
    case _ if contains[ForPerm] => false
    case _ if isPure && contains[AccessPredicate] => false
    case _ if !isPure && contains[PredicateAccess] => false
    case _ => true
  }

  /* Results is expected to satisfy the following constraints:
   *   result.variables == variables
   *   result.exp == this.exp
   *
   * TODO: Might be better to also replace occurrences of the quantified variables in `exp`
   */
  def withVariables(variables: Seq[LocalVarDecl]): QuantifiedExp
}

object QuantifiedExp {
  def unapply(q: QuantifiedExp): Option[(Seq[LocalVarDecl], Exp)] = Some(q.variables, q.exp)
}

/** Universal quantification. */
case class Forall(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends QuantifiedExp {
  //require(isValid, s"Invalid quantifier: { $this } .")
  override lazy val check : Seq[ConsistencyError] =
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Body of universal quantifier must be of Bool type, but found ${exp.typ}", exp.pos)) else Seq()) ++
    Consistency.checkAllVarsMentionedInTriggers(variables, triggers) ++
    checkNoNestedQuantsForQuantPermissions

  /** checks against nested quantification for quantified permissions */
  lazy val checkNoNestedQuantsForQuantPermissions : Seq[ConsistencyError] = {
    QuantifiedPermissionAssertion.unapply(this) match {
      case None => Seq()
      case Some((_, exp, _)) => if(exp.existsDefined({case _: Forall => }) && !exp.isPure)
        Seq(ConsistencyError("Nested quantifiers are not allowed for quantified permissions.", exp.pos)) else Seq()
    }
  }
  /** Returns an identical forall quantification that has some automatically generated triggers
    * if necessary and possible.
    */
  lazy val autoTrigger: Forall = {
    if (triggers.isEmpty) {
      Expressions.generateTriggerSet(this) match {
        case Some((vars, triggerSets)) =>
          Forall(vars, triggerSets.map(set => Trigger(set.exps)()), exp)(pos, MakeInfoPair(AutoTriggered,info))
        case None =>
          /* Couldn't generate triggers */
          this
      }
    } else {
      // triggers already present
      this
    }
  }

  def withVariables(variables: Seq[LocalVarDecl]): Forall =
    copy(variables)(this.pos, this.info, this.errT)
}

/** Existential quantification. */
case class Exists(variables: Seq[LocalVarDecl], triggers: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends QuantifiedExp {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(exp) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Body of existential quantifier must be of Bool type, but found ${exp.typ}", exp.pos)) else Seq())

  /** Returns an identical forall quantification that has some automatically generated triggers
    * if necessary and possible.
    */
  lazy val autoTrigger: Exists = {
    if (triggers.isEmpty) {
      Expressions.generateTriggerSet(this) match {
        case Some((vars, triggerSets)) =>
          Exists(vars, triggerSets.map(set => Trigger(set.exps)()), exp)(pos, MakeInfoPair(AutoTriggered,info))
        case None =>
          /* Couldn't generate triggers */
          this
      }
    } else {
      // triggers already present
      this
    }
  }

  def withVariables(variables: Seq[LocalVarDecl]): Exists =
    copy(variables)(this.pos, this.info, this.errT)
}


/** Quantification over heap chunks with positive permission in any of the listed fields */

case class ForPerm(variables: Seq[LocalVarDecl], resource: ResourceAccess, body: Exp)
                  (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Exp with QuantifiedExp {
  override lazy val check : Seq[ConsistencyError] =
    (if (!(body isSubtype Bool)) Seq(ConsistencyError(s"Body of forperm quantifier must be of Bool type, but found ${body.typ}.", body.pos)) else Seq()) ++
    Consistency.checkPure(body) ++
    (if (!Consistency.noPerm(body)) Seq(ConsistencyError("Body of forperm quantifier is not allowed to contain perm expressions.", body.pos)) else Seq()) ++
    (if (!Consistency.noForPerm(body)) Seq(ConsistencyError("Body of forperm quantifier is not allowed to contain nested forperm expressions.", body.pos)) else Seq())

  def exp: Exp = body

  override lazy val typ = Bool

  override def isValid : Boolean = !body.contains[PermExp]

  def withVariables(variables: Seq[LocalVarDecl]): ForPerm = {
    copy(variables)(this.pos, this.info, this.errT)
  }
}


/** A trigger for a universally quantified formula. */
case class Trigger(exps: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Node with Positioned with Infoed {
  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
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
case class LocalVar(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractLocalVar with Lhs {
  override lazy val check : Seq[ConsistencyError] =
    if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Local var name must be valid identifier.", pos)) else Seq()
}

/** A special local variable for the result of a function. */
case class Result(typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractLocalVar {
  lazy val name = "result"
}

// --- Mathematical sequences

/**
 * Marker trait for all sequence-related expressions. Does not imply that the type of the
 * expression is `SeqType`.
 */
sealed trait SeqExp extends Exp with PossibleTrigger

/** The empty sequence of a given element type. */
case class EmptySeq(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  lazy val typ = SeqType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this
}

/** An explicit, non-empty sequence. */
case class ExplicitSeq(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(elems.isEmpty) Seq(ConsistencyError("Explicit sequence must be non-empty.", pos)) else Seq()) ++
    (if(!elems.tail.forall(e => e.typ == elems.head.typ)) Seq(ConsistencyError("All elements of sequence must have same type.", elems.head.pos)) else Seq()) ++
    elems.flatMap(Consistency.checkPure)

  lazy val typ = SeqType(elems.head.typ)
  lazy val desugared : SeqExp = {
    elems.toList match {
      case Nil => sys.error("did not expect empty sequence")
      case _ :: Nil => this
      case a :: as => // desugar into singleton sequences and appends
        as.foldLeft[SeqExp](ExplicitSeq(Seq(a))(pos, info, errT)) {
          (bs:SeqExp, b:Exp) => SeqAppend(bs,ExplicitSeq(Seq(b))(pos, info, errT))(pos, info, errT)
        }
    }
  }
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitSeq(newArgs)(pos, info, errT)
}

/** A range of integers from 'low' to 'high', not including 'high', but including 'low'. */
case class RangeSeq(low: Exp, high: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!(low isSubtype Int)) Seq(ConsistencyError(s"First parameter of range-sequence expression must be Int, but found ${low.typ}", low.pos)) else Seq()) ++
    (if(!(high isSubtype Int)) Seq(ConsistencyError(s"Second parameter of range-sequence expression must be Int, but found ${high.typ}", high.pos)) else Seq())
  lazy val typ = SeqType(Int)
  def getArgs = Seq(low,high)
  def withArgs(newArgs: Seq[Exp]) = RangeSeq(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Appending two sequences of the same type. */
case class SeqAppend(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp with PrettyBinaryExpression {
  override lazy val check : Seq[ConsistencyError] =
    if(right.typ != left.typ) Seq(ConsistencyError(s"Left and right sequence types of sequence-append expression must match, but found ${left.typ} and ${right.typ}.", left.pos)) else Seq()
  lazy val priority = 8
  lazy val fixity = Infix(LeftAssociative)
  lazy val op = "++"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = SeqAppend(newArgs.head,newArgs(1))(pos, info, errT)

}

/** Access to an element of a sequence at a given index position (starting at 0). */
case class SeqIndex(s: Exp, idx: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()) ++
    (if(!(idx isSubtype Int)) Seq(ConsistencyError(s"Second parameter of sequence-access expression must be Int, but found ${idx.typ}", idx.pos)) else Seq())
  lazy val typ = s.typ.asInstanceOf[SeqType].elementType
  def getArgs = Seq(s,idx)
  def withArgs(newArgs: Seq[Exp]) = SeqIndex(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Take the first 'n' elements of the sequence 'seq'. */
case class SeqTake(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()) ++
    (if(!(n isSubtype Int)) Seq(ConsistencyError(s"Second parameter of sequence-take expression must be Int, but found ${n.typ}", n.pos)) else Seq())
  lazy val typ = s.typ
  def getArgs = Seq(s,n)
  def withArgs(newArgs: Seq[Exp]) = SeqTake(newArgs.head,newArgs(1))(pos, info, errT)

}

/** Drop the first 'n' elements of the sequence 'seq'. */
case class SeqDrop(s: Exp, n: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()) ++
    (if(!(n isSubtype Int)) Seq(ConsistencyError(s"Second parameter of sequence-drop expression must be Int, but found ${n.typ}", n.pos)) else Seq())
  lazy val typ = s.typ
  def getArgs = Seq(s,n)
  def withArgs(newArgs: Seq[Exp]) = SeqDrop(newArgs.head,newArgs(1))(pos, info, errT)

}

/** Is the element 'elem' contained in the sequence 'seq'? */
case class SeqContains(elem: Exp, s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp with PrettyBinaryExpression {
  override lazy val check : Seq[ConsistencyError] =
    (if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()) ++
    (if(!(elem isSubtype s.typ.asInstanceOf[SeqType].elementType)) Seq(ConsistencyError(s"Expected type ${s.typ.asInstanceOf[SeqType].elementType} but found ${elem.typ}", elem.pos)) else Seq())
  lazy val priority = 7
  lazy val fixity = Infix(LeftAssociative)
  lazy val left: PrettyExpression = elem
  lazy val op = "in"
  lazy val right: PrettyExpression = s
  lazy val typ = Bool
  def getArgs = Seq(elem,s)
  def withArgs(newArgs: Seq[Exp]) = SeqContains(newArgs.head,newArgs(1))(pos, info, errT)
}

/** The same sequence as 'seq', but with the element at index 'idx' replaced with 'elem'. */
case class SeqUpdate(s: Exp, idx: Exp, elem: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()) ++
    (if(!(idx isSubtype Int)) Seq(ConsistencyError(s"Second parameter of sequence-update expression must be of Int type, but found ${idx.typ}", idx.pos)) else Seq()) ++
    (if(!(elem isSubtype s.typ.asInstanceOf[SeqType].elementType)) Seq(ConsistencyError(s"Expected type ${s.typ.asInstanceOf[SeqType].elementType} but found ${elem.typ}", elem.pos)) else Seq()) ++
    Consistency.checkPure(elem)

  lazy val desugaredAssumingIndexInRange : SeqExp = {
    SeqAppend(SeqTake(s,idx)(pos, info, errT),SeqAppend(ExplicitSeq(List(elem))(pos, info, errT),SeqDrop(s,Add(idx,IntLit(1)(pos, info,errT))(pos, info, errT))(pos, info, errT))(pos, info, errT))(pos, info, errT)
  }
  lazy val typ = s.typ
  def getArgs = Seq(s,idx,elem)
  def withArgs(newArgs: Seq[Exp]) = SeqUpdate(newArgs.head,newArgs(1),newArgs(2))(pos, info, errT)

}

/** The length of a sequence. */
case class SeqLength(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SeqExp {
  override lazy val check : Seq[ConsistencyError] =
    if(!s.typ.isInstanceOf[SeqType]) Seq(ConsistencyError(s"Expected sequence type but found ${s.typ}", s.pos)) else Seq()
  lazy val typ = Int
  def getArgs = Seq(s)
  def withArgs(newArgs: Seq[Exp]) = SeqLength(newArgs.head)(pos, info, errT)

}

// --- Mathematical sets and multisets

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `SetType`.
 */
sealed trait SetExp extends Exp with PossibleTrigger

/**
 * Marker trait for all set-related expressions. Does not imply that the type of the
 * expression is `MultisetType`.
 */
sealed trait MultisetExp extends Exp with PossibleTrigger

/**
 * Marker traits for all expressions that correspond to operations on sets or multisets.
 * Does not imply that the type of the expression is `SetType` or `MultisetType`.
 */
sealed trait AnySetExp extends SetExp with MultisetExp
sealed trait AnySetUnExp extends AnySetExp with UnExp
sealed trait AnySetBinExp extends AnySetExp with PrettyBinaryExpression with BinExp

/** The empty set of a given element type. */
case class EmptySet(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SetExp {
  lazy val typ = SetType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this
}

/** An explicit, non-empty set. */
case class ExplicitSet(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends SetExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(elems.isEmpty) Seq(ConsistencyError("Explicit set must be non-empty.", pos)) else Seq()) ++
    (if(!elems.tail.forall(e => e.typ == elems.head.typ)) Seq(ConsistencyError("All elements of set must have same type.", elems.head.pos)) else Seq()) ++
    elems.flatMap(Consistency.checkPure)
  lazy val typ = SetType(elems.head.typ)
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitSet(newArgs)(pos, info, errT)

}

/** The empty multiset of a given element type. */
case class EmptyMultiset(elemTyp: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends MultisetExp {
  lazy val typ = MultisetType(elemTyp)
  def getArgs = Seq()
  def withArgs(newArgs: Seq[Exp]) = this

}

/** An explicit, non-empty multiset. */
case class ExplicitMultiset(elems: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends MultisetExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(elems.isEmpty) Seq(ConsistencyError("Explicit multiset must be non-empty.", pos)) else Seq()) ++
    (if(!elems.tail.forall(e => e.typ == elems.head.typ)) Seq(ConsistencyError("All elements of multiset must have same type.", elems.head.pos)) else Seq()) ++
    elems.flatMap(Consistency.checkPure)
  lazy val typ = MultisetType(elems.head.typ)
  def getArgs = elems
  def withArgs(newArgs: Seq[Exp]) = ExplicitMultiset(newArgs)(pos, info, errT)

}

/** Union of two sets or two multisets. */
case class AnySetUnion(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetBinExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != right.typ) Seq(ConsistencyError("Left and right operand types must match", left.pos)) else Seq()) ++
    (if(!(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])) Seq(ConsistencyError(s"Expected SetType or MultisetType, but found ${left.typ}", left.pos)) else Seq())
  lazy val priority = 8
  lazy val fixity = Infix(LeftAssociative)
  lazy val op = "union"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetUnion(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Intersection of two sets or two multisets. */
case class AnySetIntersection(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetBinExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != right.typ) Seq(ConsistencyError("Left and right operand types must match", left.pos)) else Seq()) ++
    (if(!(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])) Seq(ConsistencyError(s"Expected SetType or MultisetType, but found ${left.typ}", left.pos)) else Seq())

  lazy val priority = 8
  lazy val fixity = Infix(LeftAssociative)
  lazy val op = "intersection"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetIntersection(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Subset relation of two sets or two multisets. */
case class AnySetSubset(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetBinExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != right.typ) Seq(ConsistencyError("Left and right operand types must match", left.pos)) else Seq()) ++
    (if(!(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])) Seq(ConsistencyError(s"Expected SetType or MultisetType, but found ${left.typ}", left.pos)) else Seq())

  lazy val priority = 8
  lazy val fixity = Infix(NonAssociative)
  lazy val op = "subset"
  lazy val typ = Bool
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetSubset(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Set difference. */
case class AnySetMinus(left: Exp, right: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetBinExp {
  override lazy val check : Seq[ConsistencyError] =
    (if(left.typ != right.typ) Seq(ConsistencyError("Left and right operand types must match", left.pos)) else Seq()) ++
    (if(!(left.typ.isInstanceOf[SetType] || left.typ.isInstanceOf[MultisetType])) Seq(ConsistencyError(s"Expected SetType or MultisetType, but found ${left.typ}", left.pos)) else Seq())

  lazy val priority = 8
  lazy val fixity = Infix(NonAssociative)
  lazy val op = "setminus"
  lazy val typ = left.typ
  def getArgs = Seq(left,right)
  def withArgs(newArgs: Seq[Exp]) = AnySetMinus(newArgs.head,newArgs(1))(pos, info, errT)
}

/** Is the element 'elem' contained in the set 's'? */
case class AnySetContains(elem: Exp, s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetBinExp {
  override lazy val check : Seq[ConsistencyError] =
    if(!((s.typ.isInstanceOf[SetType] && (elem isSubtype s.typ.asInstanceOf[SetType].elementType)) ||
    (s.typ.isInstanceOf[MultisetType] && (elem isSubtype s.typ.asInstanceOf[MultisetType].elementType)))) Seq(ConsistencyError(s"Set type ${s.typ} and element type ${elem.typ} must be compatible.", elem.pos)) else Seq()
    lazy val priority = 7
  lazy val fixity = Infix(NonAssociative)
  lazy val left = elem
  lazy val op = "in"
  lazy val right = s
  lazy val typ = if (s.typ.isInstanceOf[SetType]) Bool else Int
  def getArgs = Seq(elem,s)
  def withArgs(newArgs: Seq[Exp]) = AnySetContains(newArgs.head,newArgs(1))(pos, info, errT)
}

/** The length of a sequence. */
case class AnySetCardinality(s: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnySetUnExp {
  override lazy val check : Seq[ConsistencyError] =
    if(!(s.typ.isInstanceOf[SetType] || s.typ.isInstanceOf[MultisetType])) Seq(ConsistencyError(s"Set type expected SetType or MultisetType, but found ${s.typ}", s.pos)) else Seq()
  val exp = s
  lazy val typ = Int
  def getArgs = Seq(s)
  def withArgs(newArgs: Seq[Exp]) = AnySetCardinality(newArgs.head)(pos, info, errT)
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
sealed trait PossibleTrigger extends Exp {
  def getArgs: Seq[Exp]
  def withArgs(args: Seq[Exp]): PossibleTrigger
}

sealed trait ForbiddenInTrigger extends Exp

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
  lazy val priority = 6
  lazy val fixity = Infix(NonAssociative)
  lazy val typ = Bool
}

/** Expressions with a unary or binary operator. */
sealed trait DomainOpExp extends AbstractDomainFuncApp {
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
  def func = (_: Program) => funct
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
sealed abstract class DomainUnExp(val funct: UnOp) extends PrettyUnaryExpression with DomainOpExp with UnExp with ForbiddenInTrigger {
  def func = (_ :Program) => funct
  def funcname = funct.name
  def typ = funct.typ
  def formalArgs = funct.formalArgs
  def op = funct.op
  def fixity = funct.fixity
  def priority = funct.priority
}

/** Expressions which can appear on the left hand side of an assignment */
sealed trait Lhs extends Exp

/** Generic Expression to use to extend the AST.
  * New expression-typed AST nodes can be defined by creating new case classes extending this trait.
  * AST nodes of these types should always be converted to standard Silver nodes, and therefore never
  * reach the backend verifiers. */
trait ExtensionExp extends Exp {
  def extensionIsPure: Boolean
  def extensionSubnodes: Seq[Node]
  def typ: Type
  def verifyExtExp(): VerificationResult
  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression.*/
  def prettyPrint: PrettyPrintPrimitives#Cont
}
