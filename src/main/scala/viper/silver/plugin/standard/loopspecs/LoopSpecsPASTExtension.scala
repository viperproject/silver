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
                    (val pos : (Position, Position)) extends PExtender with PPrettySubnodes with PExp  { // with PExp()?? //extends PCallKeyword with PHeapOpApp
  override def pretty: String = s"${op.pretty}${e.pretty}"

  //typ = e.inner.typ

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.check(e.inner, expected)
    typ = e.inner.typ
    None
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkInternal(e.inner)
    typ = e.inner.typ
    None
  }



  override def translateExp(t: Translator): Exp =
    PreExp(t.exp(e.inner))(t.liftPos(this))


  // PPrimitiv(PReserved(PPredicateInstanceKeyword)(NoPosition, NoPosition))(NoPosition, NoPosition)

  //override val args = Seq(e.inner)
  //override def requirePure = args
  //override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))


  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}
}


/*case class POldExp(op: PKwOp.Old, label: Option[PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]]], e: PGrouped.Paren[PExp])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(e.inner)
  override def requirePure = args
  override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))
}*/




//case class PPreAssign(targets: PDelimited[PExp, PSym.Comma],
//                      op: Option[PSymOp.Assign],
//                      rhs: PExp)(val pos: (Position, Position)) extends PExtender with PStmt with PPrettySubnodes{
//  override def pretty: String = {
//    val preStr = pres.pretty
//    val postStr = posts.pretty
//    val ghostStr = ghost.map(_.pretty).getOrElse("")
//    val basecaseStr = basecase.map(_.pretty).getOrElse("")
//    s"${keyword.pretty}${cond.pretty}\n$preStr\n$postStr\n${body.pretty}\n$ghostStr\n$basecaseStr"
//  }
//
//  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
//    t.check(cond.inner, Bool)
//
//    pres.toSeq foreach (pre => {
//      t.check(pre.e, Impure)
//      t.checkNoPermForpermExceptInhaleExhale(pre.e)
//    })
//
//    posts.toSeq foreach (post => {
//      t.check(post.e, Impure)
//      t.checkNoPermForpermExceptInhaleExhale(post.e)
//    })
//
//    t.check(body)
//
//    ghost.foreach(gb => t.check(gb.body))
//    basecase.foreach(bc => t.check(bc.body))
//    None
//  }
//
//
//  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = ???
//
//  // Translator will turn all PNodes into their equivalent nodes.
//  // This is useful for types and things that already exist.
//  // Here we want to turn PAST node into an AST node
//
//  override def translateStmt(t: Translator): Stmt =
//
//
//  val pos = pStmt
//  val (s, annotations) = extractAnnotationFromStmt(pStmt)
//  val sourcePNodeInfo = SourcePNodeInfo(pStmt)
//  val info = if (annotations.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotations))
//  s match {
//    case PAssign(targets, _, PCall(method, args, _)) if members(method.name).isInstanceOf[Method] =>
//      methodCallAssign(s, targets.toSeq, ts => MethodCall(findMethod(method), args.inner.toSeq map exp, ts)(pos, info))
//    case PAssign(targets, _, _) if targets.length != 1 =>
//      sys.error(s"Found non-unary target of assignment")
//    case PAssign(targets, _, PNewExp(_, fieldsOpt)) =>
//      val fields = fieldsOpt.inner match {
//        // Note that this will not use any fields that extensions declare
//        case Left(_) => program.fields flatMap (_.fields.toSeq map translate)
//        case Right(pfields) => pfields.toSeq map findField
//      }
//      methodCallAssign(s, Seq(targets.head), lv => NewStmt(lv.head, fields)(pos, info))
//    case PAssign(PDelimited(idnuse: PIdnUse), _, rhs) =>
//      LocalVarAssign(LocalVar(idnuse.name, ttyp(idnuse.decl.get.asInstanceOf[PAssignableVarDecl].typ))(pos, SourcePNodeInfo(idnuse)), exp(rhs))(pos, info)
//    case PAssign(PDelimited(field: PFieldAccess), _, rhs) =>
//      FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnref))(field, SourcePNodeInfo(field)), exp(rhs))(pos, info)
//
//}


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

  override def translateStmt(t: Translator): Stmt =

    LoopSpecs(
      t.exp(cond.inner),
      //todo how to make this simpler than And(true, true)
      //todo rm comments
      // todo case switch
      {val exps =  (pres.toSeq map (pre => t.exp(pre.e)))
        if (exps.length > 1) {
          exps.tail.foldLeft[Exp](exps.head)((e1, e2) => And(e1, e2)(e1.pos))
        }else if(exps.length == 1){
          exps.head
        }else{
          TrueLit()()
        }
      },
      (posts.toSeq map (post => t.exp(post.e))).foldLeft[Exp](TrueLit()())((e1, e2) =>And(e1, e2)(e1.pos)),
      t.stmt(body).asInstanceOf[Seqn],
      ghost.map(g => t.stmt(g.body).asInstanceOf[Seqn]),
      basecase.map(bc => t.stmt(bc.body).asInstanceOf[Seqn])
      )(t.liftPos(this))


}
