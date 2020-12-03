package viper.silver.plugin.standard.inline

import viper.silver.ast._

sealed trait InlinePredicateDeclaration extends ExtensionMember {}

case class InlinePredicate(predicate: Predicate)
                          (override val pos: Position = predicate.pos,
                           override val info: Info = predicate.info,
                           override val errT: ErrorTrafo = predicate.errT) extends InlinePredicateDeclaration {
  override def name: String = predicate.name
  override val scopedDecls: Seq[Declaration] = predicate.scopedDecls
  override def extensionSubnodes: Seq[Node] = Seq(predicate)
}
