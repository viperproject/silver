package viper.silver.plugin.standard.reasoning

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, group, line, nil, show, showBlock, showVars, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.{Consistency, Expressions}
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}


/** An `FailureExpectedInfo` info that tells us that this assert is a existential elimination. */
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


  override val scopedDecls = varList


  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("prove forall") <+> showVars(varList) <+>
      text("assuming") <+>
      toParenDoc(exp1) <+>
      text("implies") <+> toParenDoc(exp2) <+>
      showBlock(block)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ triggers ++ Seq(exp1) ++ Seq(exp2) ++ Seq(block)
}


sealed trait FlowAnnotation extends ExtensionExp with Node with Scope {
   override def extensionIsPure: Boolean = true

  override val scopedDecls = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "FlowAnalysis: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("FlowAnalysis: verifyExtExp has not been implemented.", pos)))

  }
}


case class FlowAnnotationVar(v: Exp, varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = Seq(v) ++ varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> show(v) <+>
    text("by") <+>
      ssep(varList map show, group(char (',') <> line(" ")))
  }
}

case class FlowAnnotationVarHeapArg(v: Exp, varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = Seq(v) ++ varList
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> show(v) <+>
      text("by") <+>
      ssep(varList map show, group(char(',') <> line(" "))) <+> text(", heap")
  }
}

case class FlowAnnotationHeap(varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced heap") <+>
      text("by") <+>
      ssep(varList map show, group(char (',') <> line(" ")))
  }
}

case class FlowAnnotationHeapHeapArg(varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced heap") <+>
      text("by") <+>
      ssep(varList map show, group(char (',') <> line(" "))) <+> text(", heap")

  }
}