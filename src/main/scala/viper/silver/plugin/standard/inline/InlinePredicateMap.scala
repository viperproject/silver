package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.rewriter.Traverse.BottomUp
import viper.silver.ast.utility.rewriter.{SimpleContext, Strategy}
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.ast.{And, Bool, ErrTrafo, ErrorTrafo, Exp, FullPerm, FuncApp, Function, Implies, Info, Let, LocalVarDecl, Node, PermMul, Position, Predicate, PredicateAccessPredicate, ReTrafo, WildcardPerm}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors.PredicateNotWellformed
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

case class InlinePredicateMap(private val data: mutable.Map[String, Predicate] = mutable.Map()) {

  val handleWildcardStrategy: Strategy[Node, SimpleContext[Node]] = ViperStrategy.Slim({
    case pm@PermMul(_, WildcardPerm()) => WildcardPerm()(pm.pos, pm.info, pm.errT)
    case PermMul(left, FullPerm()) => left
    case fa@FuncApp(_, Seq(WildcardPerm(), _ *)) => monoWildCardApp(fa)
  }, BottomUp)

  def predicateBodyNoErrT(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    val args = predAcc.loc.args.prepended(predAcc.perm)
    val args2 = args.map(recur(_).asInstanceOf[Exp])
    val res = Expressions.instantiateVariables(predicate.body.get, predicate.formalArgs, args2, scope)
    val res2 = handleWildcardStrategy.execute[Exp](res)
    res2
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

  def wildCardName(name: String): String = s"${name}__wildcard"

  def monoWildCardApp(funcApp: FuncApp): FuncApp = funcApp.args.head match {
    case WildcardPerm() => FuncApp(wildCardName(funcApp.funcname), funcApp.args.tail)(funcApp.pos, funcApp.info, funcApp.typ, funcApp.errT)
    case _ => funcApp
  }

  def monoWildCard(func: Function): Function = {
    val permArg = func.formalArgs.head.localVar
    val strat = ViperStrategy.Slim({
      case `permArg` => WildcardPerm()(permArg.pos, permArg.info, permArg.errT)
    }, BottomUp) + handleWildcardStrategy
    val func2 = strat.execute[Function](func)
    func2.copy(name = wildCardName(func.name), formalArgs = func.formalArgs.tail)(func.pos, func.info, func.errT)
  }

  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp, dummyName: String)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val funcApp = FuncApp(predAcc.loc.predicateName, predAcc.loc.args.prepended(predAcc.perm))(pos, info, Bool, errT)
    val funcApp2 = monoWildCardApp(funcApp)
    Let(LocalVarDecl(dummyName, Bool)(), funcApp2, inner)(pos, info, errT)
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
    data.iterator.flatMap{case (_, p@Predicate(name, args, Some(exp))) =>
      Seq(unfoldingFunction(p, name, args, wrapPredUnfold(exp, args.head.localVar)),
        monoWildCard(unfoldingFunction(p, name, args, exp)))
    }.toSeq
  }
}
