package semper.sil.parser

import org.kiama.util.Positioned
import org.kiama.attribution.Attributable
import TypeHelper._
import java.nio.file.Path

/**
 * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
 * with the actual SIL abstract syntax tree.
 *
 * @author Stefan Heule
 */
sealed trait PNode extends Positioned with Attributable {
  /**
   * Returns a list of all direct sub-nodes of this node.
   */
  def subnodes = Nodes.subnodes(this)

  /**
   * Applies the function `f` to the node and the results of the subnodes.
   */
  def reduce[T](f: (PNode, Seq[T]) => T) = Visitor.reduce[T](this)(f)

  /**
   * More powerful version of reduceTree that also carries a context argument through the tree.
   */
  def reduce[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduce[C, R](this)(context, enter, combine)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def visit(f: PartialFunction[PNode, Unit]) {
    Visitor.visit(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit(f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]) {
    Visitor.visit(this, f1, f2)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes if `f`
   * returned true.
   */
  def visitOpt(f: PNode => Boolean) {
    Visitor.visitOpt(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes if `f1`
   * returned true, and finally calls `f2` to the AST node.
   */
  def visitOpt(f1: PNode => Boolean, f2: PNode => Unit) {
    Visitor.visitOpt(this, f1, f2)
  }

  def transform(pre: PartialFunction[PNode, PNode] = PartialFunction.empty)(
    recursive: PNode => Boolean = !pre.isDefinedAt(_),
    post: PartialFunction[PNode, PNode] = PartialFunction.empty): this.type =
    Transformer.transform[this.type](this, pre)(recursive, post)
}

object TypeHelper {
  val Int = PPrimitiv("Int")
  val Bool = PPrimitiv("Bool")
  val Perm = PPrimitiv("Perm")
  val Ref = PPrimitiv("Ref")
  val Pred = PPredicateType()
}

// Identifiers (uses and definitions)
trait Identifier {
  def name: String
}

case class PIdnDef(name: String) extends PNode with Identifier
case class PIdnUse(name: String) extends PExp with Identifier

// Formal arguments
case class PFormalArgDecl(idndef: PIdnDef, typ: PType) extends PNode with TypedEntity

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
  // this class is also used to represent type variables, as they cannot syntactically
  // distinguished from domain types without generic arguments.  For type variables, we have
  // args.length = 0
  def isTypeVar = _isTypeVar.getOrElse(sys.error(s"type has not been checked yet, call check($this) first"))
  var _isTypeVar: Option[Boolean] = None
  override def isConcrete: Boolean = {
    args.forall(_.isConcrete) && args.size > 0 && !isTypeVar
  }
  override def substitute(newTypVarsMap: Map[String, PType]): PType = {
    if (isTypeVar && newTypVarsMap.isDefinedAt(domain.name)) {
      return newTypVarsMap.get(domain.name).get
    }
    val newArgs = args map {
      case PTypeVar(name) if newTypVarsMap.isDefinedAt(name) =>
        newTypVarsMap.get(name).get
      case t => t
    }
    PDomainType(domain, newArgs)
  }
  override def toString = domain.name + (if (args.isEmpty) "" else s"[${args.mkString(", ")}]")
}
object PTypeVar {
  def unapply(p: PDomainType) = if (p.isTypeVar) Some(p.domain.name) else None
  def apply(name: String) = {
    val t = PDomainType(PIdnUse(name), Nil)
    t._isTypeVar = Some(true)
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
case class PUnfolding(acc: PAccPred, exp: PExp) extends PExp
case class PExists(variable: Seq[PFormalArgDecl], exp: PExp) extends PExp
case class PForall(variable: Seq[PFormalArgDecl], triggers: Seq[Seq[PExp]], exp: PExp) extends PExp with PScope
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

case class PEmptySet() extends PExp
case class PExplicitSet(elems: Seq[PExp]) extends PExp
case class PEmptyMultiset() extends PExp
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
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt with TypedEntity
case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp]) extends PStmt
case class PLabel(idndef: PIdnDef) extends PStmt with RealEntity
case class PGoto(targets: PIdnUse) extends PStmt

// Declarations
sealed trait PMember extends PNode with PScope {
  def idndef: PIdnDef
}
// a member (like method or axiom) that is its own name scope
sealed trait PScope

case class PProgram(file: Path, domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod]) extends PNode
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: PStmt) extends PMember with RealEntity
case class PDomain(idndef: PIdnDef, typVars: Seq[PIdnDef], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom]) extends PMember with RealEntity
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[PExp], posts: Seq[PExp], exp: PExp) extends PMember with TypedEntity
case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean) extends PMember with TypedEntity
case class PAxiom(idndef: PIdnDef, exp: PExp) extends PNode with PScope
case class PField(idndef: PIdnDef, typ: PType) extends PMember with TypedEntity
case class PPredicate(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: PExp) extends PMember with TypedEntity {
  val typ = PPredicateType()
}

/** An entity is a declaration (i.e. something that contains a PIdnDef). */
sealed trait Entity
sealed trait RealEntity extends Entity
sealed trait TypedEntity extends RealEntity {
  def typ: PType
}
abstract class ErrorEntity(name: String) extends Entity

/**
 * A entity represented by names for whom we have seen more than one
 * declaration so we are unsure what is being represented.
 */
case class MultipleEntity() extends ErrorEntity("multiple")

/**
 * An unknown entity, represented by names whose declarations are missing.
 */
case class UnknownEntity() extends ErrorEntity("unknown")


/**
 * Utility methods for parser parserAST nodes.
 *
 * @author Stefan Heule
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
      case PResultLit() => Nil
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PPredicateAccess(args, pred) => args ++ Seq(pred)
      case PFunctApp(func, args) => Seq(func) ++ args
      case PUnfolding(acc, exp) => Seq(acc, exp)
      case PExists(vars, exp) => vars ++ Seq(exp)
      case po: POldExp => Seq(po.e)
      case PForall(vars, triggers, exp) => vars ++ triggers.flatten ++ Seq(exp)
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

      case PEmptySet() => Nil
      case PExplicitSet(elems) => elems
      case PEmptyMultiset() => Nil
      case PExplicitMultiset(elems) => elems

      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
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
      case PFunction(name, args, typ, pres, posts, exp) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres ++ posts ++ Seq(exp)
      case PDomainFunction(name, args, typ, unique) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(name, args, body) =>
        Seq(name) ++ args ++ Seq(body)
      case PAxiom(idndef, exp) => Seq(idndef, exp)
    }
  }
}

/**
 * An implementation for visitors of the SIL AST.
 *
 * @author Stefan Heule
 */
object Visitor {

  /**
   * See Node.reduceTree.
   */
  def reduce[T](n: PNode)(f: (PNode, Seq[T]) => T): T = {
    val subResults = n.subnodes.map(reduce[T](_)(f))
    f(n, subResults)
  }

  /**
   * See Node.reduceTree.
   */
  def reduce[C, R](n: PNode)(context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R): R = {
    val newContext = enter(n, context)
    val subResults = n.subnodes.map(reduce[C, R](_)(newContext, enter, combine))
    combine(n, context, subResults)
  }

  /**
   * See Node.visit.
   */
  def visit(n: PNode)(f: PartialFunction[PNode, Unit]) {
    if (f.isDefinedAt(n)) f(n)
    for (sub <- n.subnodes) {
      visit(sub)(f)
    }
  }

  /**
   * See Node.visit.
   */
  def visit(n: PNode, f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]) {
    if (f1.isDefinedAt(n)) f1(n)
    for (sub <- n.subnodes) {
      visit(sub, f1, f2)
    }
    if (f2.isDefinedAt(n)) f2(n)
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt(n: PNode)(f: PNode => Boolean) {
    if (f(n)) {
      for (sub <- n.subnodes) {
        visitOpt(sub)(f)
      }
    }
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt(n: PNode, f1: PNode => Boolean, f2: PNode => Unit) {
    if (f1(n)) {
      for (sub <- n.subnodes) {
        visitOpt(sub, f1, f2)
      }
    }
    f2(n)
  }
}
