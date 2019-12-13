package viper.silver.ast

import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc, show}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult


case class InsidePredicates(p1: PredicateAccess, p2: PredicateAccess)
                           (override val pos: Position = NoPosition,
                            override val info: Info = NoInfo,
                            override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def typ: Type = Bool

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(p1, p2)

  override def verifyExtExp(): VerificationResult = ???


  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("InsidePredicate") <> parens(ssep(Seq(p1, p2) map show, char (',') <> space))
}

case class EqualPredicates(p1: PredicateAccess, p2: PredicateAccess)
                          (override val pos: Position = NoPosition,
                           override val info: Info = NoInfo,
                           override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def typ: Type = Bool

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(p1, p2)

  override def verifyExtExp(): VerificationResult = ???

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("EqualPredicate") <> parens(ssep(Seq(p1, p2) map show, char (',') <> space))
}
