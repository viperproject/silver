package semper.sil.ast

import semper.sil.ast.utility.{Expressions, Consistency, Statements, CfgGenerator}

// --- Statements

/** A common trait for statements. */
sealed trait Stmt extends Node with Infoed with Positioned {
  require(Consistency.noResult(this), "Result variables are only allowed in postconditions of functions.")

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

  /**
   * Computes all local variables that are written to in this statement.
   */
  def writtenVars = Statements.writtenVars(this)
}

/** A statement that creates a new object and assigns it to a local variable. */
case class NewStmt(lhs: LocalVar)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Ref isSubtype lhs)
}

/** An assignment to a field or a local variable */
sealed trait AbstractAssign extends Stmt {
  require(Consistency.isAssignable(rhs, lhs), s"${rhs.typ} ($rhs) is not assignable to ${lhs.typ} ($lhs)")
  Consistency.checkNoPositiveOnly(rhs)
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
case class LocalVarAssign(lhs: LocalVar, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractAssign

/** An assignment to a field variable. */
case class FieldAssign(lhs: FieldAccess, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractAssign

/** A method/function/domain function call. */
trait Call {
  require(Consistency.areAssignable(args, formalArgs), s"$args vs $formalArgs for $callee")
  def callee: Callable
  def args: Seq[Exp]
  def formalArgs: Seq[LocalVarDecl] = callee.formalArgs
}

/** A method call. */
case class MethodCall(method: Method, args: Seq[Exp], targets: Seq[LocalVar])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(Consistency.areAssignable(method.formalReturns, targets))
  require(Consistency.noDuplicates(targets))
  args foreach Consistency.checkNoPositiveOnly
  lazy val callee = method
  /**
   * The precondition of this method call (i.e., the precondition of the method with
   * the arguments instantiated correctly).
   */
  lazy val pres = {
    method.pres map (e => Expressions.instantiateVariables(e, method.formalArgs, args))
  }
  /**
   * The postcondition of this method call (i.e., the postcondition of the method with
   * the arguments instantiated correctly).
   */
  lazy val posts = {
    method.posts map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, args ++ targets))
  }
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

/** Package a magic wand. */
case class Package(wand: MagicWand)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(wand isSubtype Bool)
}

/** Apply a magic wand. */
case class Apply(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  require(exp isSubtype Wand, s"Expected wand but found ${exp.typ} ($exp)")
}

/** A sequence of statements. */
case class Seqn(ss: Seq[Stmt])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt

/** An if control statement. */
case class If(cond: Exp, thn: Stmt, els: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Stmt {
  Consistency.checkNoPositiveOnly(cond)
}

/** A while loop. */
case class While(cond: Exp, invs: Seq[Exp], locals: Seq[LocalVarDecl], body: Stmt)
                (val pos: Position = NoPosition, val info: Info = NoInfo)
      extends Stmt {
  Consistency.checkNoPositiveOnly(cond)
  invs map Consistency.checkNonPostContract
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
case class FreshReadPerm(vars: Seq[LocalVar], body: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo)
    extends Stmt
