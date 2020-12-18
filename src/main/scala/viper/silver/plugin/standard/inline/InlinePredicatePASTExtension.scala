package viper.silver.plugin.standard.inline

import viper.silver.parser._
import viper.silver.ast.Member

sealed trait PInlinePredicateDeclaration extends PExtender with PMember with PGlobalDeclaration {}

case class PInlinePredicate(
  idndef: PIdnDef,
  formalArgs: Seq[PFormalArgDecl],
  maybeBody: Option[PExp]
) extends PInlinePredicateDeclaration {
  override def getSubnodes(): Seq[PNode] = Seq(PPredicate(idndef, formalArgs, maybeBody))
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None // TODO
  override def translateMember(t: Translator): Member =
    InlinePredicate(???, ???, ???)(t.liftPos(PPredicate(idndef, formalArgs, maybeBody))) // TODO
}
