package viper.silver.plugin.standard.inline

import viper.silver.parser._
import viper.silver.ast.Member

sealed trait PInlinePredicateDeclaration extends PExtender with PMember with PGlobalDeclaration {}

case class PInlinePredicate(predicate: PPredicate) extends PInlinePredicateDeclaration {
  override def idndef: PIdnDef = predicate.idndef
  override def getSubnodes(): Seq[PNode] = Seq(predicate)
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None // TODO
  override def translateMember(t: Translator): Member = InlinePredicate(???)(t.liftPos(predicate)) // TODO
}
