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

  private var annotatedPredIds: Set[String] = Set()

  lazy val inlinePredicate: noApi.P[PInlinePredicate] =
    P(keyword(InlinePredicateKeyword) ~/ predicateDecl)
      .map(pPred => PInlinePredicate(pPred))

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set[String](InlinePredicateKeyword))
    ParserExtension.addNewDeclAtEnd(inlinePredicate)
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    val (inPreds, otherExts) = input.extensions.partition(_.isInstanceOf[PInlinePredicate])
    val newPreds = input.predicates ++ inPreds.collect{
      case p: PInlinePredicate =>
        this.annotatedPredIds += p.idndef.name
        p.inner
    }
    input.copy(predicates = newPreds, extensions = otherExts)
  }

  override def beforeVerify(input: Program): Program = {
    val annotatedPredIds = this.annotatedPredIds
    val recursivePredIds = checkRecursive(annotatedPredIds, input) ++ checkMutualRecursive(annotatedPredIds, input)
    val cond = { pred: String =>
      input.findPredicate(pred).body.nonEmpty &&
      !recursivePredIds(pred) &&
      annotatedPredIds(pred)
    }
    // val inlinePredIds = input.extensions.collect({
    //   case InlinePredicate(p) if p.body.isDefined => p.name
    // }).toSet
    // val nonrecursiveInlinePredIds = inlinePredIds.diff(recursivePredIds)
    // val cond = { pred: String => nonrecursiveInlinePredIds(pred) }
    val rewrittenMethods = input.methods.map(rewriteMethod(_, input, cond))
    val rewrittenFunctions = input.functions.map(rewriteFunction(_, input, cond))
    val allPredicates = input.predicates ++ input.extensions.collect {
      case inlinedPred: InlinePredicate => inlinedPred.toPredicate
    }
    val rewrittenPredicates = allPredicates.collect({
      case pred if !cond(pred.name) => rewritePredicate(pred, input, cond)
    })
    ViperStrategy.Slim({
      case program: Program =>
        program.copy(
          methods = rewrittenMethods,
          functions = rewrittenFunctions,
          predicates = rewrittenPredicates
        )(program.pos, program.info, program.errT)
    }).execute[Program](input)
  }
}
