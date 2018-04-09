/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

import viper.silver.ast.utility.{Consistency, Statements}
import viper.silver.cfg.silver.CfgGenerator
import viper.silver.verifier.ConsistencyError

// --- Statements

/** A common trait for statements. */
sealed trait Stmt extends Hashable with Infoed with Positioned with TransformableErrors {

  /**
    * Returns a list of all actual statements contained in this statement.  That
    * is, all statements except `Seqn`, including statements in the body of loops, etc.
    */
  def children = Statements.children(this)

  /**
    * Returns a control flow graph that corresponds to this statement.
    */
  def toCfg(simplify: Boolean = true) = CfgGenerator.statementToCfg(this, simplify)

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

/** A method/function/domain function call. - AS: this comment is misleading - the trait is currently not used for method calls below */
trait Call {
//  require(Consistency.areAssignable(args, formalArgs), s"$args vs $formalArgs for callee: $callee") <- this check has been moved to case classes

  def callee: String

  def args: Seq[Exp]

  def formalArgs: Seq[LocalVarDecl] // formal arguments of the call, for type checking
}

/** A method call. */
case class MethodCall(methodName: String, args: Seq[Exp], targets: Seq[LocalVar])(val pos: Position, val info: Info, val errT: ErrorTrafo) extends Stmt {
  override lazy val check : Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    if(!Consistency.noResult(this))
      s :+= ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)
    if (!Consistency.noDuplicates(targets))
      s :+= ConsistencyError("Targets are not allowed to have duplicates", targets.head.pos)
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
case class Seqn(ss: Seq[Stmt], scopedDecls: Seq[Declaration])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt with Scope {

  // Interpret leaves of a possibly nested Seqn structure as its children
  override lazy val getChildren: Seq[AnyRef] = {
    def seqFlat(ss: Seq[Stmt]): (Seq[Stmt], Seq[Declaration]) = {
      val result = ss.foldLeft((Seq.empty[Stmt], Seq.empty[Declaration]))((x: (Seq[Stmt], Seq[Declaration]), y: Stmt) => {
        y match {
          case elems: Seq[Stmt @unchecked] => {
            val tmp = seqFlat(elems)
            (x._1 ++ tmp._1, x._2 ++ tmp._2)
          }
          case elemS: Seqn => {
            val tmp = seqFlat(elemS.ss)
            (x._1 ++ tmp._1, x._2 ++ elemS.scopedDecls ++ tmp._2)
          }
          case elem: Stmt => (x._1 ++ Seq(elem), x._2)
        }
      })
      result
    }
    val all = seqFlat(ss)
    Seq(all._1, scopedDecls ++ all._2)
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

/** A fresh statement assigns a fresh, dedicated symbolic permission values to
  * each of the passed variables.
  */
case class Fresh(vars: Seq[LocalVar])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    vars.flatMap(v=>{ if(!(v isSubtype Perm)) Seq(ConsistencyError(s"Fresh statements can only be used with variables of type Perm, but found ${v.typ}.", v.pos)) else Seq()})
}

/** A constraining-block takes a sequence of permission-typed variables,
  * each of which is marked as constrainable while executing the statements
  * in the body of the block. Potentially constraining statements are, e.g.,
  * exhale-statements.
  */
case class Constraining(vars: Seq[LocalVar], body: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends Stmt {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(this)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)) else Seq()) ++
    vars.flatMap(v=>{ if(!(v isSubtype Perm)) Seq(ConsistencyError(s"Constraining statements can only be used with variables of type Perm, but found ${v.typ}.", v.pos)) else Seq()})
}

/** Local variable declaration statement.
  *
  * [2016-12-22 Malte] Introduced so that local variables can be declared inside loops in the
  * CFG-representation. This decision should be reevaluated when we consider introducing proper
  * scopes.
  */
case class LocalVarDeclStmt(decl: LocalVarDecl)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Stmt
