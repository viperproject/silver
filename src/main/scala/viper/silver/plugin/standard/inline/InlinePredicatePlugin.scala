package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{Exp, LocalVar, Method, Node, PredicateAccess, Program}
import viper.silver.plugin.standard.predicateinstance.PredicateInstance
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate {

  private[this] val InlinePredicateKeyword = "inline"

  override def beforeVerify(input: Program): Program = {
    val declaredMethods = input.methods
    val methodsWithExpandedPres = declaredMethods.map(expandPreconditions(_, input))

    // TODO: actually rewrite program with methods with expanded predicates
    val rewrittenProgram = ViperStrategy.Slim({
      case program: Program =>
        program.copy(methods = methodsWithExpandedPres)(program.pos, program.info, program.errT)
    }, Traverse.BottomUp).execute(input)
    rewrittenProgram
  }

  private[this] def expandPreconditions(method: Method, program: Program): Method = {
    method.copy(name = method.name,
      formalArgs = method.formalArgs,
      formalReturns = method.formalReturns,
      pres = method.pres.map { pre =>
        expandPred(pre, program).fold(pre)(expandedPred => expandedPred)
      },
      posts = method.posts,
      body = method.body
    )(pos = method.pos, info = method.info, errT = method.errT)
  }

  private[this] def expandPred(expr: Exp, program: Program): Option[Exp] = expr match {
    case pred: PredicateAccess =>
      val args = getLocalVarNames(pred)
      pred.predicateBody(program, args)
    case _:_ => None
  }

  private[this] def getLocalVarNames(predicate: PredicateAccess): Set[String] =
    predicate.args.map {
      case arg: LocalVar => arg.name
      case _: _ => ""
    }.filterNot(_ == "").toSet
}
