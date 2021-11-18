package viper.silver.plugin.standard.inline

import viper.silver.parser._
import viper.silver.ast.{Member, Predicate}
import viper.silver.parser.PScope.Id

sealed trait PInlinePredicateDeclaration extends PExtender with PAnyFunction with PGlobalDeclaration {}

case class PInlinePredicate(
  inner: PPredicate
) extends PInlinePredicateDeclaration {
  override val scopeId: Id = inner.scopeId
  override def getSubnodes(): Seq[PNode] = Seq(inner.idndef) ++ inner.formalArgs ++ inner.body
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkDeclaration(inner)
    t.checkBody(inner)
    None
  } // TODO
  override def translateMember(t: Translator): Member =
    Predicate(
      inner.idndef.name,
      inner.formalArgs.map(t.liftVarDecl),
      inner.body.map(t.exp))(t.liftPos(pos = this)
    )

  override def translateMemberSignature(t: Translator): Member = {
    val pos = this.inner
    Predicate(inner.idndef.name, inner.formalArgs map t.liftVarDecl, null)()
  } // TODO


  override def idndef: PIdnDef = inner.idndef

  override def formalArgs: Seq[PAnyFormalArgDecl] = inner.formalArgs

  override def typ: PType = TypeHelper.Bool
}
