package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Bool, ErrorTrafo, Exp, FuncApp, Function, Info, Let, LocalVarDecl, Node, Position, Predicate, PredicateAccessPredicate, ReTrafo}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

case class InlinePredicateMap(private val data: mutable.Map[String, (Seq[LocalVarDecl], Exp)] = mutable.Map()) extends AnyVal {

  def predicateBodyNoErrT(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    val args = predAcc.loc.args.prepended(predAcc.perm)
    val args2 = args.map(recur(_).asInstanceOf[Exp])
    val res = Expressions.instantiateVariables(predicate._2, predicate._1, args2, scope)
    res
  }

  def predicateBody(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val res: Exp = predicateBodyNoErrT(predAcc, scope, recur)
    val errT = ReTrafo{_ => InsufficientPermission(predAcc.loc)}
    res.withMeta(res.pos, res.info, errT)
  }

  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp, dummyName: String)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val funcApp = FuncApp(predAcc.loc.predicateName, predAcc.loc.args.prepended(predAcc.perm))(pos, info, Bool, errT)
    Let(LocalVarDecl(dummyName, Bool)(), funcApp, inner)(pos, info, errT)
  }

  def shouldRewrite(predAcc: PredicateAccessPredicate): Boolean = data.contains(predAcc.loc.predicateName)

  def addPredicate(pred: Predicate, permVar: LocalVarDecl): Unit = {
    data.put(pred.name, (pred.formalArgs.prepended(permVar), pred.body.get))
  }

  def toUnfoldingFunctions: Seq[Function] = {
    data.iterator.map{case (name, (args, exp)) =>
      Function(name, args, Bool, Seq(wrapPredUnfold(exp, args.head.localVar)), Seq(), None)()}.toSeq
  }
}
