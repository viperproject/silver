package viper.silver.plugin.standard.inline

import viper.silver.ast._

sealed trait InlinePredicateDeclaration extends ExtensionMember {}

case class InlinePredicate(name: String, formalArgs: Seq[LocalVarDecl], maybeBody: Option[Exp])
                          (override val pos: Position = NoPosition,
                           override val info: Info = NoInfo,
                           override val errT: ErrorTrafo = NoTrafos) extends InlinePredicateDeclaration {
  override val scopedDecls: Seq[Declaration] = formalArgs
  override def extensionSubnodes: Seq[Node] = Seq(Predicate(name, formalArgs, maybeBody)(pos, info, errT))

  def toPredicate: Predicate =
    Predicate(name, formalArgs, maybeBody)(pos, info, errT)
}
