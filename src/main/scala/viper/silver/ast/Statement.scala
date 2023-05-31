// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.{Consistency, Statements}
import viper.silver.cfg.silver.{CfgGenerator, SilverCfg}
import viper.silver.verifier.ConsistencyError

// --- Statements

/** A common trait for statements. */
sealed trait Stmt extends Hashable with Infoed with Positioned with TransformableErrors {

  /**
    * Returns a control flow graph that corresponds to this statement.
    */
  def toCfg(simplify: Boolean = true, detect: Boolean = true): SilverCfg = CfgGenerator.statementToCfg(this, simplify, detect)

  /**
    * Returns a list of all undeclared local variables contained in this statement and
    * throws an exception if the same variable is used with different types.
    */
  def undeclLocalVars = Statements.undeclLocalVars(this)

  /**
    * Computes all local variables that are written to in this statement.
    */
  def writtenVars = Statements.writtenVars(this)

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}

/** A statement that creates a new object and assigns it to a local variable. */
case class NewStmt(lhs: LocalVar, fields: Seq[Field])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(Ref isSubtype lhs)) Seq(ConsistencyError(s"Left-hand side of New statement must be Ref type, but found ${lhs.typ}", lhs.pos)) else Seq())

}

/** An assignment to a field or a local variable */
sealed trait AbstractAssign extends Stmt {

  def lhs: Lhs

  def rhs: Exp
}

object AbstractAssign {
  def apply(lhs: Lhs, rhs: Exp)(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) = lhs match {
    case l: LocalVar => LocalVarAssign(l, rhs)(pos, info, errT)
    case l: FieldAccess => FieldAssign(l, rhs)(pos, info, errT)
  }

  def unapply(a: AbstractAssign) = Some((a.lhs, a.rhs))
}

/** An assignment to a local variable. */
case class LocalVarAssign(lhs: LocalVar, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractAssign{
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    Consistency.checkPure(rhs) ++
    (if(!Consistency.isAssignable(rhs, lhs)) Seq(ConsistencyError(s"Right-hand side $rhs is not assignable to left-hand side $lhs.", lhs.pos)) else Seq())
}

/** An assignment to a field variable. */
case class FieldAssign(lhs: FieldAccess, rhs: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AbstractAssign{
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    Consistency.checkPure(rhs) ++
    (if(!Consistency.isAssignable(rhs, lhs)) Seq(ConsistencyError(s"Right-hand side $rhs is not assignable to left-hand side $lhs.", lhs.pos)) else Seq())
}

/** A method call. */
case class MethodCall(methodName: String, args: Seq[Exp], targets: Seq[LocalVar])(val pos: Position, val info: Info, val errT: ErrorTrafo) extends Stmt {
  override lazy val check : Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    if(!Consistency.noResult(this))
      s :+= ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)
    if (!Consistency.noDuplicates(targets))
      s :+= ConsistencyError("Targets are not allowed to have duplicates", pos)
    s ++= args.flatMap(Consistency.checkPure)
    s
  }
}

object MethodCall {
  def apply(method: Method, args: Seq[Exp], targets: Seq[LocalVar])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): MethodCall = {
    MethodCall(method.name, args, targets)(pos, info, errT)
  }
}


/** An exhale statement. */
case class Exhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Assertion to exhale must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
}

/** An inhale statement. */
case class Inhale(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Assertion to inhale must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
}

/** An assert statement. */
case class Assert(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Assertion to assert must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
}

case class Assume(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError(s"Assertion to assume must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
}

/** An fold statement. */
case class Fold(acc: PredicateAccessPredicate)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()
}

/** An unfold statement. */
case class Unfold(acc: PredicateAccessPredicate)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()
}

/** Package a magic wand. */
case class Package(wand: MagicWand, proofScript: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(wand isSubtype Wand)) Seq(ConsistencyError(s"Expected wand but found ${wand.typ} ($wand)", wand.pos)) else Seq())
}

/** Apply a magic wand. */
case class Apply(exp: MagicWand)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if(!(exp isSubtype Wand)) Seq(ConsistencyError(s"Expected wand but found ${exp.typ} ($exp)", exp.pos)) else Seq())

}

/** A sequence of statements. */
case class Seqn(ss: Seq[Stmt], scopedSeqnDeclarations: Seq[Declaration])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt with Scope {
  /** scoped declarations of extended statements (contributed by plugins) as well as the declarations of the sequence itself */
  override lazy val scopedDecls: Seq[Declaration] = scopedSeqnDeclarations ++ ss.flatMap {
    case es: ExtensionStmt => es.declarationsInParentScope
    case _ => Seq.empty
  }
}

/** An if control statement. */
case class If(cond: Exp, thn: Seqn, els: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(cond) ++
    (if(!(cond isSubtype Bool)) Seq(ConsistencyError(s"If condition must be of type Bool, but found ${cond.typ}", cond.pos)) else Seq()) ++
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq())
}

/** A while loop. */
case class While(cond: Exp, invs: Seq[Exp], body: Seqn)
                (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    Consistency.checkPure(cond) ++
    invs.flatMap(Consistency.checkNonPostContract) ++
    (if (!(cond isSubtype Bool)) Seq(ConsistencyError(s"While loop condition must be of type Bool, but found ${cond.typ}", cond.pos)) else Seq()) ++
    invs.flatMap(Consistency.checkNoPermForpermExceptInhaleExhale)
}

/** A named label. Labels can be used by gotos as jump targets, and by labelled old-expressions
  * to refer to the state as it existed at that label.
  */
case class Label(name: String, invs: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt with Declaration {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    invs.flatMap(i=>{ if(!(i isSubtype Bool)) Seq(ConsistencyError(s"Label invariants must be of type Bool, but found ${i.typ}", i.pos)) else Seq()})
}

/**
  * A goto statement.  Note that goto's in Viper are limited to forward jumps, and a jump cannot enter
  * a loop but might leave one or several loops.  This ensures that the only back edges in the
  * control flow graph are due to while loops.
  */
case class Goto(target: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt

/** Local variable declaration statement.
  *
  * [2016-12-22 Malte] Introduced so that local variables can be declared inside loops in the
  * CFG-representation. This decision should be reevaluated when we consider introducing proper
  * scopes.
  */
case class LocalVarDeclStmt(decl: LocalVarDecl)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt

/** Quasihavoc statement.
  * Replaces the quasihavocked resource's snapshot with a fresh snapshot.
  * The optional lhs provides a guard, under which the resource is quasihavocked. For example,
  *   quasihavoc c ==> Pred(x)
  * means that we only quasihavoc Pred(x) if the condition c is true.
  * The quasihavocall variant of this statement allows one to quasihavoc an unbounded number of resources
  */
case class Quasihavoc(lhs: Option[Exp], exp: ResourceAccess)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check: Seq[ConsistencyError] = {
    // Sanity checks of properties that should be guaranteed by earlier phases of the front end. These checks
    // are similar to the ones provided by inhale and exhale statements.
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if (lhs.nonEmpty && !(lhs.get isSubtype Bool)) Seq(ConsistencyError(s"Left side of quasihavoc implication must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
  }
}

/** Quasihavocall statement (see quasiavoc statement)
  * Must extend Scope because it declares quantified variables.
  */
case class Quasihavocall(vars: Seq[LocalVarDecl], lhs: Option[Exp], exp: ResourceAccess)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt with Scope {
  val scopedDecls: Seq[Declaration] = vars

  override lazy val check : Seq[ConsistencyError] = {
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    (if (lhs.nonEmpty && !(lhs.get isSubtype Bool)) Seq(ConsistencyError(s"Left side of quasihavocall implication must be of type Bool, but found ${exp.typ}", exp.pos)) else Seq())
  }
}


/** Generic Statement type to use to extend the AST.
  * New statement-typed AST nodes can be defined by creating new case classes extending this trait.
  * AST nodes of these types should always be converted to standard Silver nodes, and therefore never
  * reach the backend verifiers. */
trait ExtensionStmt extends Stmt {
  def extensionSubnodes: Seq[Node]
  def prettyPrint: PrettyPrintPrimitives#Cont
  /** declarations contributed by this statement that should be added to the parent scope */
  def declarationsInParentScope: Seq[Declaration] = Seq.empty
}