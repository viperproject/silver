package viper.silver.plugin.standard.inline

import fastparse.noApi
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.Program
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.parser.ParserExtension
import viper.silver.parser.FastParser._
import viper.silver.parser._
import White._

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate
  with InlineRewrite
  with InlineErrorChecker {
  import fastparse.noApi._

  private[this] val InlinePredicateKeyword = "inline"

  lazy val inlinePredicate: noApi.P[PInlinePredicate] =
    P(keyword(InlinePredicateKeyword) ~/ predicateDecl)
      .map(pPred => PInlinePredicate(pPred.idndef, pPred.formalArgs, pPred.body))

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set[String](InlinePredicateKeyword))
    ParserExtension.addNewDeclAtEnd(inlinePredicate)
    input
  }

  override def beforeVerify(input: Program): Program = {
    val allPredIds = input.predicates.collect{ case p if p.body.nonEmpty => p.name }.toSet
    val recursivePredIds = (checkRecursive(allPredIds, input) ++ checkMutualRecursive(allPredIds, input)).map(_.name)
    val nonrecursivePredIds = allPredIds.diff(recursivePredIds)
    val cond = { pred: String => nonrecursivePredIds(pred) }
    // val inlinePredIds = input.extensions.collect({
    //   case InlinePredicate(p) if p.body.isDefined => p.name
    // }).toSet
    // val nonrecursiveInlinePredIds = inlinePredIds.diff(recursivePredIds)
    // val cond = { pred: String => nonrecursiveInlinePredIds(pred) }
    val rewrittenMethods = input.methods.map(rewriteMethod(_, input, cond))
    val rewrittenFunctions = input.functions.map(rewriteFunction(_, input, cond))
    ViperStrategy.Slim({
      case program@Program(_, _, _, predicates, _, extensions) =>
        program.copy(
          methods = rewrittenMethods,
          functions = rewrittenFunctions,
          predicates = predicates ++ extensions.collect {
            case inlinePred: InlinePredicate => inlinePred.toPredicate
          },
        )(program.pos, program.info, program.errT)
    }).execute[Program](input)
  }
}
