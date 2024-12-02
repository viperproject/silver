package viper.silver.plugin.standard.loopspecs


import viper.silver.ast._
import viper.silver.parser.TypeHelper.{Bool, Impure, Ref}
import viper.silver.parser._

import scala.collection.mutable

case object PGhostKeyword extends PKw("ghost") with PKeywordLang // PSym.Brace
case object PBaseCaseKeyword extends PKw("basecase") with PKeywordLang // PSym.Brace
case object PPreKeyword extends PKwOp("pre") with PKeywordLang //with PKeywordAtom // PSym.Paren

case class PPreExp(op : PReserved[PPreKeyword.type],
                   e : PGrouped.Paren[PExp])
                    (val pos : (Position, Position)) extends PExtender with PPrettySubnodes with PExp{ // with PExp()?? //extends PCallKeyword with PHeapOpApp
  override def pretty: String = s"${op.pretty}${e.pretty}"


  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.check(e.inner, Ref) //TODO: What about if there's a var here?? Of type int... how to generalize??
    None
  }

  override def translateExp(t: Translator): Exp =
    PreExp(t.exp(e.inner))(t.liftPos(this))

  //override val args = Seq(e.inner)
  //override def requirePure = args
  //override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))


  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
}


/*case class POldExp(op: PKwOp.Old, label: Option[PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]]], e: PGrouped.Paren[PExp])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(e.inner)
  override def requirePure = args
  override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))
}*/

case class PGhostBlock(
  keyword: PReserved[PGhostKeyword.type],
  body: PSeqn
)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty: String = s"${keyword.pretty}${body.pretty}"
}

case class PBaseCaseBlock(
  keyword: PReserved[PBaseCaseKeyword.type],
  body: PSeqn
)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty: String = s"${keyword.pretty}${body.pretty}"
}
//TODO: add new type of expr add PAST and AST (look at old)
//currently cant add consistency chekc for pre() when used in post ==> do this in beforeVerfiy in plugin itself consistency error on AST lvl

case class PLoopSpecs(
  keyword: PReserved[PKw.While.type],
  cond: PGrouped.Paren[PExp],
  pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]],
  posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]],
  body: PSeqn,
  ghost: Option[PGhostBlock],
  basecase: Option[PBaseCaseBlock]
)(val pos: (Position, Position)) extends PExtender with PStmt with PPrettySubnodes {
  override def pretty: String = {
    val preStr = pres.pretty
    val postStr = posts.pretty
    val ghostStr = ghost.map(_.pretty).getOrElse("")
    val basecaseStr = basecase.map(_.pretty).getOrElse("")
    s"${keyword.pretty}${cond.pretty}\n$preStr\n$postStr\n${body.pretty}\n$ghostStr\n$basecaseStr"
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.check(cond.inner, Bool)

    pres.toSeq foreach (pre => {
      t.check(pre.e, Impure)
      t.checkNoPermForpermExceptInhaleExhale(pre.e)
    })

    posts.toSeq foreach (post => {
      t.check(post.e, Impure)
      t.checkNoPermForpermExceptInhaleExhale(post.e)
    })

    t.check(body)

    ghost.foreach(gb => t.check(gb.body))
    basecase.foreach(bc => t.check(bc.body))
    None
  }


  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = ???
  
  // Translator will turn all PNodes into their equivalent nodes.
  // This is useful for types and things that already exist.
  // Here we want to turn PAST node into an AST node

  /* case PWhile(_, cond, invs, body) =>
        While(exp(cond.inner), invs.toSeq map (inv => exp(inv.e)), stmt(body).asInstanceOf[Seqn])(pos, info) */

  override def translateStmt(t: Translator): Stmt =
    LoopSpecs(
      t.exp(cond.inner),
      pres.toSeq map (pre => t.exp(pre.e)),
      posts.toSeq map (post => t.exp(post.e)),
      t.stmt(body).asInstanceOf[Seqn],
      ghost.map(g => t.stmt(g.body).asInstanceOf[Seqn]),
      basecase.map(bc => t.stmt(bc.body).asInstanceOf[Seqn])
      )(t.liftPos(this))


}
//TODO: What is PExtender?? should I extend this instead of PStmt?

//type Ghost = PReserved[PGhost.type]

  //type Basecase = PReserved[Basecase.type]




/* 
case class PWhile(
keyword: PKw.While, 
cond: PGrouped.Paren[PExp], 
invs: PDelimited[PSpecification[PKw.InvSpec], 
Option[PSym.Semi]], 
body: PSeqn)
(val pos: (Position, Position)) extends PStmt
 */
