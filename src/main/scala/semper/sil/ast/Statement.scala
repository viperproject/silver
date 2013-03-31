package semper.sil.ast

import utility.{Consistency, Statements, CfgGenerator}

// --- Statements

/** A common trait for statements. */
sealed trait Stmt extends Node with Infoed with Positioned {
  /**
   * Returns a list of all actual statements contained in this statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def children = Statements.children(this)

  /**
   * Returns a control flow graph that corresponds to this statement.
   */
  def toCfg = CfgGenerator.toCFG(this)
  
  /**
   * Returns a list of all undeclared local variables contained in this statement and
   * throws an exception if the same variable is used with different types.
   */
  def undeclLocalVars = Statements.undeclLocalVars(this)
}

/** A statement that creates a new object and assigns it to a local variable. */
case class NewStmt(lhs: LocalVar)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Ref isSubtype lhs)
}

/** An assignment to a field or a local variable */
sealed trait AbstractAssign extends Stmt {
  def lhs: Lhs
  def rhs: Exp
}
object AbstractAssign {
  def apply(lhs: Lhs, rhs: Exp)(pos: Position = NoPosition, info: Info = NoInfo) = lhs match {
    case l: LocalVar => LocalVarAssign(l, rhs)(pos, info)
    case l: FieldAccess => FieldAssign(l, rhs)(pos, info)
  }
  def unapply(a: AbstractAssign) = Some((a.lhs, a.rhs))
}

/** An assignment to a local variable. */
case class LocalVarAssign(lhs: LocalVar, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractAssign {
  require(Consistency.isAssignable(rhs, lhs))
}

/** An assignment to a field variable. */
case class FieldAssign(lhs: FieldAccess, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractAssign {
  require(Consistency.isAssignable(rhs, lhs))
}

/** A method/function/domain function call. */
trait Call {
  require(Consistency.areAssignable(args, formalArgs))
  def callee: Callable
  def args: Seq[Exp]
  def formalArgs: Seq[LocalVarDecl] = callee.formalArgs
}

/** A method call. */
case class MethodCall(method: Method, args: Seq[Exp], targets: Seq[LocalVar])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.areAssignable(method.formalReturns, targets))
  require(Consistency.noDuplicates(targets))
  lazy val callee = method
}

/** An exhale statement. */
case class Exhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(exp isSubtype Bool)
}

/** An inhale statement. */
case class Inhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(exp isSubtype Bool)
}

/** An assert statement. */
case class Assert(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(exp isSubtype Bool)
}

/** An fold statement. */
case class Fold(acc: PredicateAccessPredicate)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(acc isSubtype Bool)
}

/** An unfold statement. */
case class Unfold(acc: PredicateAccessPredicate)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(acc isSubtype Bool)
}

/** A sequence of statements. */
case class Seqn(ss: Seq[Stmt])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt

/** An if control statement. */
case class If(cond: Exp, thn: Stmt, els: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt

/** A while loop. */
case class While(cond: Exp, invs: Seq[Exp], locals: Seq[LocalVarDecl], body: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  /**
   * The list of variables that are written to in this loop (not counting local variables).
   */
  def writtenVars: Seq[LocalVar] = {
    val candidates = undeclLocalVars
    var writtenTo: Seq[LocalVar] = Nil
    body visit {
      case LocalVarAssign(lhs, _) =>
        writtenTo = writtenTo ++ Seq(lhs)
      case MethodCall(_, _, targets) =>
        writtenTo = writtenTo ++ targets
      case FreshReadPerm(vars, _) =>
        writtenTo = writtenTo ++ vars
    }
    candidates intersect writtenTo
  }
}

/** A label (that can be the target of a goto). */
case class Label(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.validUserDefinedIdentifier(name))
}

/**
 * A goto statement.  Note that goto's in SIL are limited to forward jumps, and a jump cannot enter
 * a loop but might leave one or several loops.  This ensures that the only back edges in the
 * control flow graph are due to while loops.
 */
case class Goto(target: String)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt

/**
 * A special block that is annotated with a list of permission-typed variables.  At the start of the
 * block, these variables should each be havoced, their values should be assumed to be strictly
 * between 0 and 1, and within the block, they can have additional assumptions introduced.
 */
case class FreshReadPerm(vars: Seq[LocalVar], body: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt
