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
}

/** An assignment to a local variable. */
case class LocalVarAssign(lhs: LocalVar, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.isAssignable(rhs, lhs))
}

/** An assignment to a field variable. */
case class FieldAssign(lhs: FieldAccess, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.isAssignable(rhs, lhs))
}

/** A method/function/domain function call. */
trait Call {
  require(Consistency.areAssignable(args, callee.formalArgs))
  def callee: Callable
  def args: Seq[Exp]
}

/** A call that has a receiver, i.e. a method or function call. */
trait RcvCall {
  require(rcv isSubtype Ref)
  def rcv: Exp
}

/** A method call. */
case class MethodCall(m: Method, rcv: Exp, args: Seq[Exp], targets: Seq[LocalVar])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.areAssignable(m.formalReturns, targets))
  require(Consistency.noDuplicates(targets))
  lazy val callee = m
}

/** An exhale statement. */
case class Exhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(exp isSubtype Bool)
}

/** An inhale statement. */
case class Inhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
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
case class While(cond: Exp, invs: Seq[Exp], locals: Seq[LocalVar], body: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt

/** A label (that can be the target of a goto). */
case class Label(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.validUserDefinedIdentifier(name))
}

/** A goto statement. */
case class Goto(target: String)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt
