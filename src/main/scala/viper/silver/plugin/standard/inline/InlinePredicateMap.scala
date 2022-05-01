package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Bool, Exp, FuncApp, Function, Let, LocalVarDecl, NoInfo, NoPosition, NoTrafos, Predicate, PredicateAccessPredicate}
import viper.silver.plugin.standard.inline.WrapPred._

import scala.collection.mutable

case class InlinePredicateMap(private val data: mutable.Map[String, (Seq[LocalVarDecl], Exp)] = mutable.Map()) extends AnyVal {
  def predicateBody(predAcc: PredicateAccessPredicate, scope: Set[String]): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    Expressions.instantiateVariables(predicate._2, predicate._1, predAcc.loc.args.prepended(predAcc.perm), scope)
  }

  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp): Exp = {
    val funcApp = FuncApp(predAcc.loc.predicateName, predAcc.loc.args.prepended(predAcc.perm))(NoPosition, NoInfo, Bool, NoTrafos)
    Let(LocalVarDecl("__dummy__", Bool)(), funcApp, inner)()
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
