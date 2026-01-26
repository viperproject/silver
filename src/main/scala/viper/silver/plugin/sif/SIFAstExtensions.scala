// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silver.plugin.sif

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, nil, parens, show, showBlock, text}
import viper.silver.ast._
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}

/** Low(exp), i.e., exp is the same in both executions.
  * Optionally, a comparator function can be given: This must be the name of a domain function that, with the given
  * typVarMap (see DomainFuncApp), can be given two values of the type of exp and return a boolean.
  * The intention is that low(exp) can be encoded as comparator(exp1, exp2) instead of exp1 == exp2, i.e.,
  * the function can express a custom notion of equality.
  */
case class SIFLowExp(exp: Exp, comparator: Option[String] = None, typVarMap: Map[TypeVar, Type] = Map())
                    (val pos: Position = NoPosition,
                     val info: Info = NoInfo,
                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionSubnodes: Seq[Node] = Seq(exp)

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "SIFLowExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("SIFLowExp: verifyExtExp has not been implemented.", pos)))
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = (if (comparator.isDefined) text("lowVal")
  else text("low")) <> parens(show(exp))

  override val extensionIsPure: Boolean = exp.isPure
}

/**
  * Expresses that the current program point must be reached by both or no execution, i.e., whether it is reached
  * is low.
  */
case class SIFLowEventExp()(val pos: Position = NoPosition,
                            val info: Info = NoInfo,
                            val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionSubnodes: Seq[Node] = Nil

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "SIFLowEventExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("SIFLowEventExp: verifyExtExp has not been implemented.", pos)))
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("lowEvent")

  override val extensionIsPure: Boolean = true

}

/**
  * Refers to the value of exp in execution i (must be 0 or 1).
  */
case class SIFRelExp(exp: Exp, i: IntLit)
                    (val pos: Position = NoPosition,
                     val info: Info = NoInfo,
                     val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionSubnodes: Seq[Node] = Seq(exp, i)

  override def typ: Type = exp.typ

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "SIFRelExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("SIFRelExp: verifyExtExp has not been implemented.", pos)))
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = (text("rel") <> parens(show(exp) <> "," <+> show(i)))

  override val extensionIsPure: Boolean = exp.isPure
}

///////////////////////////////////////////////////////////////////
// The following AST nodes are currently only used in specific   //
// frontends and don't have parsing support in the plugin.       //
///////////////////////////////////////////////////////////////////

case class SIFReturnStmt(exp: Option[Exp], resVar: Option[LocalVar])
                        (val pos: Position = NoPosition,
                         val info: Info = NoInfo,
                         val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq(exp, resVar).collect({case Some(x) => x})

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("return") <+> (exp match {
    case Some(x) => show(x)
    case None => nil
  })
}

case class SIFBreakStmt()(val pos: Position = NoPosition,
                          val info: Info = NoInfo,
                          val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq()

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("break")
}

case class SIFContinueStmt()(val pos: Position = NoPosition,
                             val info: Info = NoInfo,
                             val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq()

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("continue")
}

case class SIFRaiseStmt(assignment: Option[LocalVarAssign])
                       (val pos: Position = NoPosition,
                        val info: Info = NoInfo,
                        val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = assignment match {
    case Some(a) => Seq(a)
    case None => Seq()
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("raise") <+>
    (assignment match {case Some(a) => show(a) case None => nil})
}

case class SIFExceptionHandler(errVar: LocalVar, exception: Exp, body: Seqn)
                              (val pos: Position = NoPosition,
                               val info: Info = NoInfo,
                               val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq(errVar, exception, body)

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("catch") <+> parens(show(exception)) <+>
    showBlock(body)
}

case class SIFTryCatchStmt(body: Seqn,
                           catchBlocks: Seq[SIFExceptionHandler],
                           elseBlock: Option[Seqn],
                           finallyBlock: Option[Seqn])
                          (val pos: Position = NoPosition,
                           val info: Info = NoInfo,
                           val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq(body) ++
    Seq(elseBlock, finallyBlock).collect({case Some(x) => x}) ++
    catchBlocks.flatMap(h => h.subnodes)

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("try") <+> showBlock(body) <>
      catchBlocks.map(h => h.prettyPrint)
        .fold(nil)((l, r) => l <+> r) <+>
      (elseBlock match {case Some(x) => text("else") <+> showBlock(x) case None => nil}) <+>
      (finallyBlock match {case Some(x) => text("finally") <+> showBlock(x) case None => nil})
  }
}

case class SIFDeclassifyStmt(exp: Exp)
                            (val pos: Position = NoPosition,
                             val info: Info = NoInfo,
                             val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq(exp)

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("declassify") <+> show(exp)
}

case class SIFInlinedCallStmt(stmts: Seqn)
                         (val pos: Position = NoPosition,
                          val info: Info = NoInfo,
                          val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq(stmts)

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("inlined call") <> show(stmts)
}

case class SIFAssertNoException()(val pos: Position = NoPosition,
                                  val info: Info = NoInfo,
                                  val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = Seq()

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("assert no exception")
}

/**
  * To be used only in loop invariants. States that if and when the loop is exited via a break or return is low,
  * i.e., either both executions break or return in the same iteration, or both do not break or return at all.
  */
case class SIFLowExitExp()(val pos: Position = NoPosition,
                            val info: Info = NoInfo,
                            val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionSubnodes: Seq[Node] = Nil

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "SIFLowExitExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("SIFLowExitExp: verifyExtExp has not been implemented.", pos)))
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("lowExit")

  override val extensionIsPure: Boolean = false
}

case class SIFTerminatesExp(cond: Exp)(val pos: Position = NoPosition,
                                       val info: Info = NoInfo,
                                       val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionSubnodes: Seq[Node] = Seq(cond)

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "SIFTerminatesExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("SIFTerminatesExp: verifyExtExp has not been implemented.", pos)))
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("terminates under condition") <+> show(cond)

  override def extensionIsPure: Boolean = cond.isPure
}

case class SIFInfo(comment: Seq[String],
                   continueUnaware: Boolean = false,
                   obligationVar: Boolean = false) extends Info{
  lazy val isCached = false
}

case class SIFDynCheckInfo(comment: Seq[String],
                           dynCheck: Exp,
                           onlyDynVersion: Boolean = false) extends Info{
  lazy val isCached = false
}
