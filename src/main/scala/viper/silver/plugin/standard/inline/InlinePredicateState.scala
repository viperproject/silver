package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.rewriter.Traverse.BottomUp
import viper.silver.ast.utility.rewriter.{SimpleContext, Strategy}
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.ast.{And, Bool, ErrTrafo, ErrorTrafo, Exp, FullPerm, FuncApp, Function, Implies, Info, Let, LocalVar, LocalVarDecl, Node, Perm, PermMul, Position, Predicate, PredicateAccessPredicate, ReTrafo, WildcardPerm}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors.PredicateNotWellformed
import viper.silver.verifier.reasons.InsufficientPermission

import scala.collection.mutable

case class InlinePredicateState() {
  private val data: mutable.Map[String, Predicate] = mutable.Map()
  private var todoMono: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  private val doneMono: mutable.Map[String, String] = mutable.Map()
  val names: PrefixNameGenerator = new PrefixNameGenerator("pi")
  val permDecl: LocalVarDecl = LocalVarDecl(names.createUnique("perm"), Perm)()
  def permVar: LocalVar = permDecl.localVar

  // Modifies this (may add new names to todoMono and doneMono if not already done)
  val handleWildcardStrategy: Strategy[Node, SimpleContext[Node]] = ViperStrategy.Slim({
    case pm@PermMul(_, WildcardPerm()) => WildcardPerm()(pm.pos, pm.info, pm.errT)
    case PermMul(left, FullPerm()) => left
    case fa@FuncApp(_, Seq(WildcardPerm(), _ *)) => monoWildCardApp(fa)
  }, BottomUp)

  // Modifies this (may add new names to todoMono and doneMono if not already done)
  def predicateBodyNoErrT(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val predicate = data(predAcc.loc.predicateName)
    val args = predAcc.loc.args.prepended(predAcc.perm)
    val args2 = args.map(recur(_).asInstanceOf[Exp])
    val res = Expressions.instantiateVariables(predicate.body.get, predicate.formalArgs, args2, scope)
    val res2 = handleWildcardStrategy.execute[Exp](res)
    res2
  }

  // Modifies this (may add new names to todoMono and doneMono if not already done)
  def predicateBody(predAcc: PredicateAccessPredicate, scope: Set[String], recur: Node => Node): Exp = {
    val res: Exp = predicateBodyNoErrT(predAcc, scope, recur)
    val errT = ReTrafo { _ => InsufficientPermission(predAcc.loc) }
    embedErrT(res.withMeta(predAcc.meta), errT)
  }

  def embedErrT(exp: Exp, errT: ReTrafo): Exp = exp match {
    case And(l, r) => And(embedErrT(l, errT), embedErrT(r, errT))(exp.pos, exp.info, errT)
    case Implies(l, r) => Implies(l, embedErrT(r, errT))(exp.pos, exp.info, errT)
    case exp => exp.withMeta(exp.pos, exp.info, errT)
  }

  // Modifies this (adds name to todoMono and doneMono if not already done)
  def wildCardName(name: String): String = {
    doneMono.get(name) match {
      case None =>
        val res = names.createUnique(s"${name}_wildcard")
        doneMono.put(name, res)
        todoMono.addOne(name)
        res
      case Some(res) => res
    }
  }

  // Modifies this (adds funcApps name to todoMono and doneMono if not already done)
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

  // Modifies this (may add new names to _todo and done if not already done)
  def assertingIn(predAcc: PredicateAccessPredicate, inner: Exp)(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    val name = data(predAcc.loc.predicateName).name
    val funcApp = FuncApp(name, predAcc.loc.args.prepended(predAcc.perm))(pos, info, Bool, errT)
    val funcApp2 = monoWildCardApp(funcApp)
    val dummy = LocalVarDecl(names.createUnique("dummy"), Bool)()
    Let(dummy, funcApp2, inner)(pos, info, errT)
  }

  def shouldRewrite(predAcc: PredicateAccessPredicate): Boolean = data.contains(predAcc.loc.predicateName)

  // Modifies this (adds pred to predicates)
  def addPredicate(pred: Predicate): Unit = {
    data.put(pred.name, pred.copy(formalArgs = pred.formalArgs.prepended(permDecl))(pred.pos, pred.info, pred.errT))
  }

  def unfoldingFunction(pred: Predicate, name: String, args: Seq[LocalVarDecl], pre: Exp): Function = {
    val errT = ErrTrafo(err => PredicateNotWellformed(pred, err.reason))
    Function(name, args, Bool, Seq(pre.withMeta(pre.pos, pre.info, errT)), Seq(), None)()
  }

  def toUnfoldingFunctions: Seq[Function] = {
    val res = mutable.ArrayBuffer.from(
      data.iterator.map { case (_, p@Predicate(name, args, Some(exp))) =>
        unfoldingFunction(p, name, args, wrapPredUnfold(exp, args.head.localVar))
    })
    while (todoMono.nonEmpty) {
      val todo = todoMono
      todoMono = mutable.ArrayBuffer()
      res.addAll(todo.iterator.map(data(_) match {
        case p@Predicate(name, args, Some(exp)) =>
          monoWildCard(unfoldingFunction(p, name, args, exp)) // note this could add more elements to todoMono
      }))
    }
    res.toSeq
  }
}
