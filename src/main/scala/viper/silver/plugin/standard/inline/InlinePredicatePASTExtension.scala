package viper.silver.plugin.standard.inline

import viper.silver.parser._
import viper.silver.ast.Member

sealed trait PInlinePredicateDeclaration extends PExtender with PMember with PGlobalDeclaration {}

case class PInlinePredicate(
  idndef: PIdnDef,
  formalArgs: Seq[PFormalArgDecl],
  maybeBody: Option[PExp]
) extends PInlinePredicateDeclaration {
  override def getSubnodes(): Seq[PNode] = Seq(idndef) ++ formalArgs ++ maybeBody
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None
  override def translateMember(t: Translator): Member =
    InlinePredicate(
      idndef.name,
      formalArgs.map(t.liftVarDecl),
      maybeBody.map(t.exp))(t.liftPos(pos = this)
    )

  override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)
}
