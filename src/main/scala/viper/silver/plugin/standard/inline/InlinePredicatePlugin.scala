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
    P(keyword(InlinePredicateKeyword) ~/ predicateDecl).map(pred => PInlinePredicate(pred))

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set[String](InlinePredicateKeyword))
    ParserExtension.addNewDeclAtEnd(inlinePredicate)
    input
  }

  override def beforeVerify(input: Program): Program = {
    val rewrittenMethods = input.methods.map { method =>
      val allPredIds = input.predicates.filter(_.body.isDefined).map(_.name).toSet
      val recursivePredIds = (checkRecursive(allPredIds, input) ++ checkMutualRecursive(allPredIds, input)).map(_.name)
      val nonrecursivePredIds = allPredIds.diff(recursivePredIds)
      val cond = { pred: String => nonrecursivePredIds(pred) }
      // val inlinePredIds = input.extensions
      //   .collect({case InlinePredicate(p) => p})
      //   .filter(_.body.isDefined)
      //   .map(_.name).toSet
      // val nonrecursiveInlinePredIds = inlinePredIds.diff(recursivePredIds)
      // val cond = { pred: String => nonrecursiveInlinePredIds(pred) }
      val inlinedPredMethod = inlinePredicates(method, input, cond)
      rewriteMethod(inlinedPredMethod, cond)
    }
    // TODO: Do we also need to rewrite functions?
    ViperStrategy.Slim({
      case program@Program(_, _, _, predicates, _, extensions) =>
        program.copy(
          methods = rewrittenMethods,
          predicates = predicates ++ extensions.collect{case InlinePredicate(p) => p},
        )(program.pos, program.info, program.errT)
    }).execute[Program](input)
  }
}
