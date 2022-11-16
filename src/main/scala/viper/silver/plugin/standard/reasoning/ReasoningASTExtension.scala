package viper.silver.plugin.standard.reasoning

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, nil, show, showVars, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.ast.utility.{Consistency, Expressions}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.verifier.ConsistencyError

import scala.collection.mutable

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

case class UniversalIntro(varList: Seq[LocalVarDecl], triggers: Seq[Trigger], exp1: Exp, exp2: Exp, block: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  // See also Expression Line 566
  override lazy val check: Seq[ConsistencyError] =
    (if (!(exp1 isSubtype Bool)) Seq(ConsistencyError(s"Body of universal quantifier must be of Bool type, but found ${exp1.typ}", exp1.pos)) else Seq()) ++
    (if (varList.isEmpty) Seq(ConsistencyError("Quantifier must have at least one quantified variable.", pos)) else Seq()) ++
    Consistency.checkAllVarsMentionedInTriggers(varList, triggers)
    //++ checkNoNestedQuantsForQuantPermissions ++
    //checkQuantifiedPermission





  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("prove forall") <+> showVars(varList) <+>
      text("requires") <+>
      toParenDoc(exp1) <+>
      text("ensures") <+> toParenDoc(exp2)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ Seq(exp1) ++ Seq(exp2)

  override def declarationsInParentScope: Seq[Declaration] = varList
}