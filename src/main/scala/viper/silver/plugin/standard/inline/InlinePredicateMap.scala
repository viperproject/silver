package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{And, Bool, ErrTrafo, ErrorTrafo, Exp, FuncApp, Function, Implies, Info, Let, LocalVarDecl, Node, Position, Predicate, PredicateAccessPredicate, ReTrafo}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors.PredicateNotWellformed
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

case class InlinePredicateMap(private val data: mutable.Map[String, Predicate] = mutable.Map()) extends AnyVal {

  def predicateBodyNoErrT(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    val args = predAcc.loc.args.prepended(predAcc.perm)
    val args2 = args.map(recur(_).asInstanceOf[Exp])
    val res = Expressions.instantiateVariables(predicate.body.get, predicate.formalArgs, args2, scope)
    res
  }

  def predicateBody(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val res: Exp = predicateBodyNoErrT(predAcc, scope, recur)
    val errT = ReTrafo{_ => InsufficientPermission(predAcc.loc)}
    embedErrT(res.withMeta(predAcc.meta), errT)
  }

  def embedErrT(exp: Exp, errT: ReTrafo): Exp = exp match {
    case And(l, r) => And(embedErrT(l, errT), embedErrT(r, errT))(exp.pos, exp.info, errT)
    case Implies(l, r) => Implies(l, embedErrT(r, errT))(exp.pos, exp.info, errT)
    case exp => exp.withMeta(exp.pos, exp.info, errT)
  }

  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp, dummyName: String)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val funcApp = FuncApp(predAcc.loc.predicateName, predAcc.loc.args.prepended(predAcc.perm))(pos, info, Bool, errT)
    Let(LocalVarDecl(dummyName, Bool)(), funcApp, inner)(pos, info, errT)
  }

  def shouldRewrite(predAcc: PredicateAccessPredicate): Boolean = data.contains(predAcc.loc.predicateName)

  def addPredicate(pred: Predicate, permVar: LocalVarDecl): Unit = {
    data.put(pred.name, pred.copy(formalArgs = pred.formalArgs.prepended(permVar))(pred.pos, pred.info, pred.errT))
  }

  def unfoldingFunction(pred: Predicate, name: String, args: Seq[LocalVarDecl], pre: Exp): Function = {
    val errT = ErrTrafo(err => PredicateNotWellformed(pred, err.reason))
    Function(name, args, Bool, Seq(pre.withMeta(pre.pos, pre.info, errT)), Seq(), None)()
  }

  def toUnfoldingFunctions: Seq[Function] = {
    data.iterator.map{case (_, p@Predicate(name, args, Some(exp))) =>
      unfoldingFunction(p, name, args, wrapPredUnfold(exp, args.head.localVar))
    }.toSeq
  }
}
