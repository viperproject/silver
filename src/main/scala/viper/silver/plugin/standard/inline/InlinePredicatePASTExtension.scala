package viper.silver.plugin.standard.inline

import viper.silver.parser._

sealed trait PInlinePredicateDeclaration extends PExtender with PGlobalDeclaration {}

case class PInlinePredicate(
  inner: PPredicate
) extends PInlinePredicateDeclaration {
  override def getSubnodes(): Seq[PNode] = Seq(inner.idndef) ++ inner.formalArgs ++ inner.body
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkDeclaration(inner)
    t.checkBody(inner)
    None
  }

  override def idndef: PIdnDef = inner.idndef
}
