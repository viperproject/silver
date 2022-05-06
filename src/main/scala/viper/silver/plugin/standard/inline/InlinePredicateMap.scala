package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Bool, ErrorTrafo, Exp, FuncApp, Function, Info, Let, LocalVarDecl, Position, Predicate, PredicateAccessPredicate, Trafos}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

case class InlinePredicateMap(private val data: mutable.Map[String, (Seq[LocalVarDecl], Exp)] = mutable.Map()) extends AnyVal {

  def predicateBodyNoErrT(predAcc: PredicateAccessPredicate, scope: Set[String]): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    val res = Expressions.instantiateVariables(predicate._2, predicate._1, predAcc.loc.args.prepended(predAcc.perm), scope)
    res
  }

  def predicateBody(predAcc: PredicateAccessPredicate, scope: Set[String]): Exp = {
    val res: Exp = predicateBodyNoErrT(predAcc, scope)
    val errT = Trafos(Nil, List({_ => InsufficientPermission(predAcc.loc)}), Some(predAcc))
    res.withMeta(res.pos, res.info, errT)
  }

  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val funcApp = FuncApp(predAcc.loc.predicateName, predAcc.loc.args.prepended(predAcc.perm))(pos, info, Bool, errT)
    Let(LocalVarDecl("__dummy__", Bool)(), funcApp, inner)(pos, info, errT)
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
