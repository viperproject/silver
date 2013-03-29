package semper.sil.parser

import org.kiama.util.Positioned
import org.kiama.attribution.Attributable
import TypeHelper._

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
   * More powerful version of reduce that also carries a context argument through the tree.
   */
  def reduce[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduce[C, R](this)(context, enter, combine)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def visit(f: PNode => Unit) {
    Visitor.visit(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit(f1: PNode => Unit, f2: PNode => Unit) {
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
}

object TypeHelper {
  val Int = PPrimitiv("Int")
  val Bool = PPrimitiv("Bool")
  val Perm = PPrimitiv("Perm")
  val Ref = PPrimitiv("Ref")
}

// Identifiers (uses and definitions)
trait Identifier
case class PIdnDef(name: String) extends PNode with Identifier
case class PIdnUse(name: String) extends PExp with Identifier

// Formal arguments
case class PFormalArgDecl(idndef: PIdnDef, typ: PType) extends PNode with RealEntity

// Types
sealed trait PType extends PNode
case class PPrimitiv(name: String) extends PType
case class PTypeVar(name: String) extends PType
case class PDomainType(domain: PIdnUse, args: Seq[PType]) extends PType
case class PUnkown() extends PType // for resolving if something cannot be typed

// Expressions
sealed trait PExp extends PNode {
  var typ: PType = PUnkown()
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
case class PFieldAcc(rcv: PExp, idnuse: PIdnUse) extends PExp

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
case class PInhale(e: PExp) extends PStmt
case class PNewStmt(target: PIdnUse) extends PStmt
case class PVarAssign(idnuse: PIdnUse, rhs: PExp) extends PStmt
case class PFieldAssign(fieldAcc: PFieldAcc, rhs: PExp) extends PStmt
case class PIf(cond: PExp, thn: PStmt, els: PStmt) extends PStmt
case class PWhile(cond: PExp, invs: Seq[PExp], body: PStmt) extends PStmt
case class PFreshReadPerm(vars: Seq[PIdnUse], stmt: PStmt) extends PStmt
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt with RealEntity

// Declarations
sealed trait PMember extends PNode
case class PProgram(idndef: PIdnDef, domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod]) extends PNode with RealEntity
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: PStmt) extends PMember with RealEntity
case class PDomain(idndef: PIdnDef) extends PMember with RealEntity
case class PField(idndef: PIdnDef, typ: PType) extends PMember with RealEntity
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[PExp], posts: Seq[PExp], exp: PExp) extends PMember with RealEntity
case class PPredicate(idndef: PIdnDef, formalArg: PFormalArgDecl, body: PExp) extends PMember with RealEntity

/** An entity is a declaration (i.e. something that contains a PIdnDef). */
sealed trait Entity
sealed trait RealEntity extends Entity
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
      case PTypeVar(name) => Nil
      case PDomainType(domain, args) => Seq(domain) ++ args
      case PUnkown() => Nil
      case PBinExp(left, op, right) => Seq(left, right)
      case PUnExp(op, exp) => Seq(exp)
      case PIntLit(i) => Nil
      case PBoolLit(b) => Nil
      case PNullLit() => Nil
      case PResultLit() => Nil
      case PFieldAcc(rcv, field) => Seq(rcv, field)
      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PExhale(exp) => Seq(exp)
      case PInhale(exp) => Seq(exp)
      case PNewStmt(idnuse) => Seq(idnuse)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PIf(cond, thn, els) => Seq(cond, thn, els)
      case PWhile(cond, invs, body) => Seq(cond) ++ invs ++ Seq(body)
      case PLocalVarDecl(idndef, typ, init) => Seq(idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PFreshReadPerm(vars, stmt) => vars ++ Seq(stmt)
      case PProgram(idndef, domains, fields, functions, predicates, methods) =>
        Seq(idndef) ++ domains ++ fields ++ functions ++ predicates ++ methods
      case PDomain(idndef) => Seq(idndef)
      case PField(idndef, typ) => Seq(idndef, typ)
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres ++ posts ++ Seq(body)
      case PFunction(name, args, typ, pres, posts, exp) =>
        args ++ Seq(typ) ++ pres ++ posts ++ Seq(exp)
      case PPredicate(name, arg, body) =>
        Seq(arg, body)
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
   * See Node.reduce.
   */
  def reduce[T](n: PNode)(f: (PNode, Seq[T]) => T): T = {
    val subResults = n.subnodes.map(reduce[T](_)(f))
    f(n, subResults)
  }

  /**
   * See Node.reduce.
   */
  def reduce[C, R](n: PNode)(context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R): R = {
    val newContext = enter(n, context)
    val subResults = n.subnodes.map(reduce[C, R](_)(newContext, enter, combine))
    combine(n, context, subResults)
  }

  /**
   * See Node.visit.
   */
  def visit(n: PNode)(f: PNode => Unit) {
    f(n)
    for (sub <- n.subnodes) {
      visit(sub)(f)
    }
  }

  /**
   * See Node.visit.
   */
  def visit(n: PNode, f1: PNode => Unit, f2: PNode => Unit) {
    f1(n)
    for (sub <- n.subnodes) {
      visit(sub, f1, f2)
    }
    f2(n)
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
