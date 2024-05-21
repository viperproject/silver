// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, brackets, char, defaultIndent, group, line, nest, nil, parens, show, showBlock, showVars, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}


case object ReasoningInfo extends FailureExpectedInfo

case class ExistentialElim(varList: Seq[LocalVarDecl], trigs: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override lazy val check: Seq[ConsistencyError] = Consistency.checkPure(exp) ++
    (if (!(exp isSubtype Bool)) Seq(ConsistencyError(s"Body of existential quantifier must be of Bool type, but found ${exp.typ}", exp.pos)) else Seq()) ++
    (if (varList.isEmpty) Seq(ConsistencyError("Quantifier must have at least one quantified variable.", pos)) else Seq())

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("obtain") <+> showVars(varList) <+>
      text("where") <+> (if (trigs.isEmpty) nil else space <> ssep(trigs map show, space)) <+>
      toParenDoc(exp)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ trigs ++ Seq(exp)

  /** declarations contributed by this statement that should be added to the parent scope */
  override def declarationsInParentScope: Seq[Declaration] = varList
}

case class UniversalIntro(varList: Seq[LocalVarDecl], triggers: Seq[Trigger], exp1: Exp, exp2: Exp, block: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt with Scope {
  // See also Expression Line 566
  override lazy val check: Seq[ConsistencyError] =
    (if (!(exp1 isSubtype Bool)) Seq(ConsistencyError(s"Body of universal quantifier must be of Bool type, but found ${exp1.typ}", exp1.pos)) else Seq()) ++
    (if (varList.isEmpty) Seq(ConsistencyError("Quantifier must have at least one quantified variable.", pos)) else Seq()) ++
    Consistency.checkAllVarsMentionedInTriggers(varList, triggers)

  override val scopedDecls: Seq[Declaration] = varList

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("prove forall") <+> showVars(varList) <+>
      text("assuming") <+>
      toParenDoc(exp1) <+>
      text("implies") <+> toParenDoc(exp2) <+>
      showBlock(block)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ triggers ++ Seq(exp1, exp2, block)
}

sealed trait FlowVar extends ExtensionExp {
  override def extensionIsPure: Boolean = true

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "FlowAnalysis: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("FlowAnalysis: verifyExtExp has not been implemented.", pos)))
  }
}

case class Assumes()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowVar {
  override val extensionSubnodes: Seq[Node] = Seq.empty
  override def typ: Type = InternalType
  override def prettyPrint: PrettyPrintPrimitives#Cont = PAssumesKeyword.keyword
}

case class Heap()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowVar {
  override val extensionSubnodes: Seq[Node] = Seq.empty
  override def typ: Type = InternalType
  override def prettyPrint: PrettyPrintPrimitives#Cont = PHeapKeyword.keyword
}

case class Var(decl: LocalVar)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowVar {
  override val extensionSubnodes: Seq[Node] = Seq(decl)
  override def typ: Type = decl.typ
  override def prettyPrint: PrettyPrintPrimitives#Cont = show(decl)
}

case class NoAssumeAnnotation()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Node {
  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "FlowAnalysis: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("FlowAnalysis: verifyExtExp has not been implemented.", pos)))
  }

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
   * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("assumes nothing")
  }
}

case class FlowAnnotation(v: FlowVar, varList: Seq[FlowVar])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Node with Scope {
  override def extensionIsPure: Boolean = true

  override val scopedDecls: Seq[Declaration] = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "FlowAnalysis: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("FlowAnalysis: verifyExtExp has not been implemented.", pos)))
  }

  override def extensionSubnodes: Seq[Node] = Seq(v) ++ varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> (v match {
      case value: Var => (show(value.decl))
      case _ => text("heap")
    })  <+>
      text("by") <+>
      ssep(varList.map {
        case value: Var => show(value.decl)
        case _ => text("heap")
      }, group(char(',') <> line(" ")))
  }
}

case class Lemma()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Node with Scope {
  override def extensionIsPure: Boolean = true

  override val scopedDecls: Seq[Declaration] = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "Lemma: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("Lemma: verifyExtExp has not been implemented.", pos)))
  }

  override def extensionSubnodes: Seq[Node] = Seq()

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("isLemma")
  }
}

case class OldCall(methodName: String, args: Seq[Exp], rets: Seq[LocalVar], oldLabel: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt with Scope {
  override val scopedDecls: Seq[Declaration] = Seq()

  override lazy val check: Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    if (!Consistency.noResult(this))
      s :+= ConsistencyError("Result variables are only allowed in postconditions of functions.", pos)
    if (!Consistency.noDuplicates(rets))
      s :+= ConsistencyError("Targets are not allowed to have duplicates", rets.head.pos)
    s ++= args.flatMap(Consistency.checkPure)
    s
  }

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    val call = text("oldCall") <> brackets(text(oldLabel)) <> text(methodName) <> nest(defaultIndent, parens(ssep(args map show, group(char(',') <> line))))
    rets match {
      case Nil => call
      case _ => ssep(rets map show, char(',') <> space) <+> ":=" <+> call
    }
  }

  override val extensionSubnodes: Seq[Node] = args ++ rets
}