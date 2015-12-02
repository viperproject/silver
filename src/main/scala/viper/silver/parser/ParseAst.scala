/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import org.kiama.util.Positions
import scala.util.parsing.input.Position
import org.kiama.attribution.Attributable
import viper.silver.ast.utility.Visitor
import TypeHelper._
import java.nio.file.Path

/**
 * This is a trait to ease interfacing with the changed Kiama interface - it no-longer provides Positioned as a trait, but rather a global Positions object..
 */

trait KiamaPositioned {
  def start = Positions.getStart(this)
  def setStart(p:Position) = Positions.setStart(this,p)
  def setPos(a:Any) : this.type = Positions.dupPos(a,this)
  def finish = Positions.getFinish(this)
  def setFinish(p:Position) = Positions.setFinish(this,p)
}

/**
 * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
 * with the actual SIL abstract syntax tree.
 */
sealed trait PNode extends KiamaPositioned with Attributable {
  /** Returns a list of all direct sub-nodes of this node. */
  def subnodes = Nodes.subnodes(this)

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[T](f: (PNode, Seq[T]) => T) = Visitor.reduceTree(this, Nodes.subnodes)(f)

  /** @see [[Visitor.reduceWithContext()]] */
  def reduceWithContext[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduceWithContext(this, Nodes.subnodes)(context, enter, combine)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[PNode, Unit]) {
    Visitor.visit(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]) {
    Visitor.visit(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: PNode => Boolean) {
    Visitor.visitOpt(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f1: PNode => Boolean, f2: PNode => Unit) {
    Visitor.visitOpt(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Transformer.transform()]]  */
  def transform(pre: PartialFunction[PNode, PNode] = PartialFunction.empty)
               (recursive: PNode => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[PNode, PNode] = PartialFunction.empty)
               : this.type =

    Transformer.transform[this.type](this, pre)(recursive, post)

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[PNode, A]) : Seq[A] =
    Visitor.deepCollect(Seq(this), Nodes.subnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[PNode, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), Nodes.subnodes)(f)
}

object TypeHelper {
  val Int = PPrimitiv("Int")
  val Bool = PPrimitiv("Bool")
  val Perm = PPrimitiv("Perm")
  val Ref = PPrimitiv("Ref")
  val Pred = PPredicateType()
  val Wand = PWandType()
}

// Identifiers (uses and definitions)
trait PIdentifier {
  def name: String
}

case class PIdnDef(name: String) extends PNode with PIdentifier

case class PIdnUse(name: String) extends PExp with PIdentifier {
  var decl: PDeclaration = null
    /* Should be set during resolving. Intended to preserve information
     * that is needed by the translator.
     */
}

//case class PLocalVar

/* Formal arguments.
 * [2014-11-13 Malte] Changed typ to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PFormalArgDecl(idndef: PIdnDef, var typ: PType) extends PNode with PTypedDeclaration with PLocalDeclaration

// Types
sealed trait PType extends PNode {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]
  def isConcrete: Boolean = true
  def substitute(newTypVarsMap: Map[String, PType]): PType = this
}

case class PPrimitiv(name: String) extends PType {
  override def toString = name
}

case class PDomainType(domain: PIdnUse, args: Seq[PType]) extends PType {
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved

  /* This class is also used to represent type variables, as they cannot
   * syntactically distinguished from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  def isUndeclared = kind == PDomainTypeKinds.Undeclared

  override def isConcrete: Boolean = {
    args.forall(_.isConcrete) && !isTypeVar
  }

  override def substitute(newTypVarsMap: Map[String, PType]): PType = {
    if (isTypeVar && newTypVarsMap.isDefinedAt(domain.name)) {
      return newTypVarsMap.get(domain.name).get
    }

    val newArgs = args map {
      case PTypeVar(name) if newTypVarsMap.isDefinedAt(name) => newTypVarsMap.get(name).get
      case t => t
    }

    PDomainType(domain, newArgs)
  }

  override def toString = domain.name + (if (args.isEmpty) "" else s"[${args.mkString(", ")}]")
}

object PDomainTypeKinds {
  trait Kind
  case object Unresolved extends Kind
  case object Domain extends Kind
  case object TypeVar extends Kind
  case object Undeclared extends Kind
}

object PTypeVar {
  def unapply(p: PDomainType) = if (p.isTypeVar) Some(p.domain.name) else None
  def apply(name: String) = {
    val t = PDomainType(PIdnUse(name), Nil)
    t.kind = PDomainTypeKinds.TypeVar
    t
  }
}

case class PSeqType(elementType: PType) extends PType {
  override def toString = s"Seq[$elementType]"
  override def isConcrete = elementType.isConcrete
  override def substitute(map: Map[String, PType]) = PSeqType(elementType.substitute(map))
}
case class PSetType(elementType: PType) extends PType {
  override def toString = s"Set[$elementType]"
  override def isConcrete = elementType.isConcrete
  override def substitute(map: Map[String, PType]) = PSetType(elementType.substitute(map))
}
case class PMultisetType(elementType: PType) extends PType {
  override def toString = s"Multiset[$elementType]"
  override def isConcrete = elementType.isConcrete
  override def substitute(map: Map[String, PType]) = PMultisetType(elementType.substitute(map))
}

sealed trait PInternalType extends PType

// for resolving if something cannot be typed
case class PUnknown() extends PInternalType {
  override def toString = "<error type>"
}
// used during resolving for predicate accesses
case class PPredicateType() extends PInternalType {
  override def toString = "$predicate"
}

case class PWandType() extends PInternalType {
  override def toString = "$wand"
}

// Expressions
sealed trait PExp extends PNode {
  var typ: PType = PUnknown()
}
case class PBinExp(left: PExp, op: String, right: PExp) extends PExp
case class PUnExp(op: String, exp: PExp) extends PExp
case class PIntLit(i: BigInt) extends PExp {
  typ = Int
}
case class PResultLit() extends PExp
case class PBoolLit(b: Boolean) extends PExp {
  typ = Bool
}
case class PNullLit() extends PExp {
  typ = Ref
}
sealed trait PLocationAccess extends PExp {
  def idnuse: PIdnUse
}
case class PFieldAccess(rcv: PExp, idnuse: PIdnUse) extends PLocationAccess
case class PPredicateAccess(args: Seq[PExp], idnuse: PIdnUse) extends PLocationAccess
case class PFunctApp(func: PIdnUse, args: Seq[PExp]) extends PExp

sealed trait PUnFoldingExp extends PExp {
  def acc: PAccPred
  def exp: PExp
}

case class PUnfolding(acc: PAccPred, exp: PExp) extends PUnFoldingExp
case class PFolding(acc: PAccPred, exp: PExp) extends PUnFoldingExp

case class PApplying(wand: PExp, exp: PExp) extends PExp
case class PPackaging(wand: PExp, exp: PExp) extends PExp

case class PExists(variable: Seq[PFormalArgDecl], exp: PExp) extends PExp with PScope
case class PForall(variable: Seq[PFormalArgDecl], triggers: Seq[Seq[PExp]], exp: PExp) extends PExp with PScope
case class PForPerm(variable: PFormalArgDecl, fields: Seq[PIdnUse], exp: PExp) extends PExp with PScope
case class PCondExp(cond: PExp, thn: PExp, els: PExp) extends PExp
case class PInhaleExhaleExp(in: PExp, ex: PExp) extends PExp
case class PCurPerm(loc: PLocationAccess) extends PExp
case class PNoPerm() extends PExp
case class PFullPerm() extends PExp
case class PWildcard() extends PExp
case class PEpsilon() extends PExp
case class PAccPred(loc: PLocationAccess, perm: PExp) extends PExp

sealed trait POldExp extends PExp { def e: PExp }
case class POld(e: PExp) extends POldExp
case class PLabelledOld(label: PIdnUse, e: PExp) extends POldExp
case class PApplyOld(e: PExp) extends POldExp

/* Let-expressions `let x == e1 in e2` are represented by the nested structure
 * `PLet(e1, PLetNestedScope(x, e2))`, where `PLetNestedScope <: PScope` (but
 * `PLet` isn't) in order to work with the current architecture of the resolver.
 *
 * More precisely, `NameAnalyser.run` visits a given program to ensure that all
 * used symbol are actually declared. While traversing the program, it
 * pushes/pops `PScope`s to/from the stack. If let-expressions were represented
 * by a flat `PLet(x, e1, e2) <: PScope`, then the let-bound variable `x` would
 * already be in scope while checking `e1`, which wouldn't be correct.
 */
case class PLet(exp: PExp, nestedScope: PLetNestedScope) extends PExp
case class PLetNestedScope(variable: PFormalArgDecl, body: PExp) extends PExp with PScope

case class PEmptySeq(t : PType) extends PExp {
  typ = if (t.isUnknown) PUnknown() else PSeqType(t) // type can be specified as PUnknown() if unknown
}
case class PExplicitSeq(elems: Seq[PExp]) extends PExp
case class PRangeSeq(low: PExp, high: PExp) extends PExp
case class PSeqIndex(seq: PExp, idx: PExp) extends PExp
case class PSeqTake(seq: PExp, n: PExp) extends PExp
case class PSeqDrop(seq: PExp, n: PExp) extends PExp
case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp) extends PExp
case class PSize(seq: PExp) extends PExp

case class PEmptySet(t : PType) extends PExp {
  typ = PSetType(t)
}

case class PExplicitSet(elems: Seq[PExp]) extends PExp
case class PEmptyMultiset(t : PType) extends PExp {
  typ = PMultisetType(t)
}

case class PExplicitMultiset(elems: Seq[PExp]) extends PExp
// Statements
sealed trait PStmt extends PNode {
  /**
   * Returns a list of all actual statements contained in this statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def childStmts: Seq[PStmt] = {
    this match {
      case PSeqn(ss) => ss
      case PIf(_, thn, els) => Seq(this, thn, els)
      case PWhile(_, _, body) => Seq(this, body)
      case _ => Seq(this)
    }
  }
}
case class PSeqn(ss: Seq[PStmt]) extends PStmt
case class PFold(e: PExp) extends PStmt
case class PUnfold(e: PExp) extends PStmt
case class PPackageWand(wand: PExp) extends PStmt
case class PApplyWand(e: PExp) extends PStmt
case class PExhale(e: PExp) extends PStmt
case class PAssert(e: PExp) extends PStmt
case class PInhale(e: PExp) extends PStmt
case class PNewStmt(target: PIdnUse, Fields: Option[Seq[PIdnUse]]) extends PStmt
case class PVarAssign(idnuse: PIdnUse, rhs: PExp) extends PStmt
case class PFieldAssign(fieldAcc: PFieldAccess, rhs: PExp) extends PStmt
case class PIf(cond: PExp, thn: PStmt, els: PStmt) extends PStmt
case class PWhile(cond: PExp, invs: Seq[PExp], body: PStmt) extends PStmt
case class PFresh(vars: Seq[PIdnUse]) extends PStmt
case class PConstraining(vars: Seq[PIdnUse], stmt: PStmt) extends PStmt
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt with PTypedDeclaration with PLocalDeclaration
case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp]) extends PStmt
case class PLabel(idndef: PIdnDef) extends PStmt with PLocalDeclaration
case class PGoto(targets: PIdnUse) extends PStmt
case class PTypeVarDecl(idndef: PIdnDef) extends PLocalDeclaration

case class PLetWand(idndef: PIdnDef, exp: PExp) extends PStmt with PLocalDeclaration
case class PDefine(idndef: PIdnDef, args: Option[Seq[PIdnDef]], exp: PExp) extends PStmt with PLocalDeclaration
case class PSkip() extends PStmt

sealed trait PScope extends PNode {
  val scopeId = PScope.uniqueId()
}

object PScope {
  type Id = Long

  private[this] var counter: Id = 0L

  private def uniqueId() = {
    val id = counter
    counter = counter + 1

    id
  }
}

// Declarations
/** An entity is a declaration (named) or an error node */
sealed trait PEntity

sealed trait PDeclaration extends PNode with PEntity {
  def idndef: PIdnDef
}

sealed trait PGlobalDeclaration extends PDeclaration
sealed trait PLocalDeclaration extends PDeclaration

sealed trait PTypedDeclaration extends PDeclaration {
  def typ: PType
}
abstract class PErrorEntity(name: String) extends PEntity


// a member (like method or axiom) that is its own name scope
sealed trait PMember extends PDeclaration with PScope {
//  def idndef: PIdnDef
}

case class PProgram(file: Path, domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod]) extends PNode
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: PStmt) extends PMember with PGlobalDeclaration
case class PDomain(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom]) extends PMember with PGlobalDeclaration
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PMember with PGlobalDeclaration with PTypedDeclaration
case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean) extends PMember with PGlobalDeclaration with PTypedDeclaration
case class PAxiom(idndef: PIdnDef, exp: PExp) extends PScope with PGlobalDeclaration //urij: this was not a declaration before - but the constructor of Program would complain on name clashes
case class PField(idndef: PIdnDef, typ: PType) extends PMember with PTypedDeclaration with PGlobalDeclaration
case class PPredicate(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PExp]) extends PMember with PTypedDeclaration with PGlobalDeclaration{
  val typ = PPredicateType()
}


/**
 * A entity represented by names for whom we have seen more than one
 * declaration so we are unsure what is being represented.
 */
case class PMultipleEntity() extends PErrorEntity("multiple")

/**
 * An unknown entity, represented by names whose declarations are missing.
 */
case class PUnknownEntity() extends PErrorEntity("unknown")


/**
 * Utility methods for parser parserAST nodes.
 */
object Nodes {

  /**
   * See PNode.subnodes.
   */
  def subnodes(n: PNode): Seq[PNode] = {
    n match {
      case PIdnDef(name) => Nil
      case PIdnUse(name) => Nil
      case PFormalArgDecl(idndef, typ) => Seq(idndef, typ)
      case PPrimitiv(name) => Nil
      case PDomainType(domain, args) => Seq(domain) ++ args
      case PSeqType(elemType) => Seq(elemType)
      case PSetType(elemType) => Seq(elemType)
      case PMultisetType(elemType) => Seq(elemType)
      case PUnknown() => Nil
      case PBinExp(left, op, right) => Seq(left, right)
      case PUnExp(op, exp) => Seq(exp)
      case PIntLit(i) => Nil
      case PBoolLit(b) => Nil
      case PNullLit() => Nil
      case PPredicateType() => Nil
      case PWandType() => Nil
      case PResultLit() => Nil
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PPredicateAccess(args, pred) => args ++ Seq(pred)
      case PFunctApp(func, args) => Seq(func) ++ args
      case e: PUnFoldingExp => Seq(e.acc, e.exp)
      case PApplying(wand, in) => Seq(wand, in)
      case PPackaging(wand, in) => Seq(wand, in)
      case PExists(vars, exp) => vars ++ Seq(exp)
      case po: POldExp => Seq(po.e)
      case PLet(exp, nestedScope) => Seq(exp, nestedScope)
      case PLetNestedScope(variable, body) => Seq(variable, body)
      case PForall(vars, triggers, exp) => vars ++ triggers.flatten ++ Seq(exp)
      case PForPerm(v,fields, expr) => v +: fields :+ expr
      case PCondExp(cond, thn, els) => Seq(cond, thn, els)
      case PInhaleExhaleExp(in, ex) => Seq(in, ex)
      case PCurPerm(loc) => Seq(loc)
      case PNoPerm() => Nil
      case PFullPerm() => Nil
      case PWildcard() => Nil
      case PEpsilon() => Nil
      case PAccPred(loc, perm) => Seq(loc, perm)
      case PEmptySeq(_) => Nil
      case PExplicitSeq(elems) => elems
      case PRangeSeq(low, high) => Seq(low, high)
      case PSeqIndex(seq, idx) => Seq(seq, idx)
      case PSeqTake(seq, nn) => Seq(seq, nn)
      case PSeqDrop(seq, nn) => Seq(seq, nn)
      case PSeqUpdate(seq, idx, elem) => Seq(seq, idx, elem)
      case PSize(seq) => Seq(seq)

      case PEmptySet(t) => Seq(t)
      case PExplicitSet(elems) => elems
      case PEmptyMultiset(t) => Seq(t)
      case PExplicitMultiset(elems) => elems

      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PPackageWand(exp) => Seq(exp)
      case PApplyWand(exp) => Seq(exp)
      case PExhale(exp) => Seq(exp)
      case PAssert(exp) => Seq(exp)
      case PInhale(exp) => Seq(exp)
      case PNewStmt(target, fields) => Seq(target) ++ fields.getOrElse(Seq())
      case PMethodCall(targets, method, args) => targets ++ Seq(method) ++ args
      case PLabel(name) => Seq(name)
      case PGoto(label) => Seq(label)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PIf(cond, thn, els) => Seq(cond, thn, els)
      case PWhile(cond, invs, body) => Seq(cond) ++ invs ++ Seq(body)
      case PLocalVarDecl(idndef, typ, init) => Seq(idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PFresh(vars) => vars
      case PConstraining(vars, stmt) => vars ++ Seq(stmt)
      case PProgram(file, domains, fields, functions, predicates, methods) =>
        domains ++ fields ++ functions ++ predicates ++ methods
      case PDomain(idndef, typVars, funcs, axioms) => Seq(idndef) ++ typVars ++ funcs ++ axioms
      case PField(idndef, typ) => Seq(idndef, typ)
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres ++ posts ++ Seq(body)
      case PFunction(name, args, typ, pres, posts, body) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres ++ posts ++ body
      case PDomainFunction(name, args, typ, unique) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(name, args, body) =>
        Seq(name) ++ args ++ body
      case PAxiom(idndef, exp) => Seq(idndef, exp)
      case PTypeVarDecl(name) => Seq(name)
      case PLetWand(idndef, wand) => Seq(idndef, wand)
      case PDefine(idndef, optArgs, exp) => Seq(idndef) ++ optArgs.getOrElse(Nil) ++ Seq(exp)
      case _: PSkip => Nil
    }
  }
}
