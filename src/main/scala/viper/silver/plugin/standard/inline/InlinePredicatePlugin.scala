package viper.silver.plugin.standard.inline

import fastparse._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.Program
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.parser.ParserExtension
import viper.silver.parser.FastParser._
import viper.silver.parser._

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate
  with InlineRewrite
  with InlineErrorChecker {

  private[this] val InlinePredicateKeyword = "inline"

  private var annotatedPredIds: Set[String] = Set()

  def inlinePredicate[_: P]: P[PInlinePredicate] = FP(InlinePredicateKeyword ~/ predicateDecl).map{ case (_, p) => PInlinePredicate(p)}

//  lazy val inlinePredicate: noApi.P[PInlinePredicate] =
//    P(keyword(InlinePredicateKeyword) ~/ predicateDecl)
//      .map(pPred => PInlinePredicate(pPred))

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set[String](InlinePredicateKeyword))
    ParserExtension.addNewDeclAtEnd(inlinePredicate(_))
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    val (inPreds, otherExts) = input.extensions.partition(_.isInstanceOf[PInlinePredicate])
    val newPreds = input.predicates ++ inPreds.collect{
      case p: PInlinePredicate =>
        this.annotatedPredIds += p.idndef.name
        p.inner
    }
    input.copy(predicates = newPreds, extensions = otherExts)(pos=input.pos)
  }

  override def beforeVerify(input: Program): Program = {
    val annotatedPredIds = this.annotatedPredIds
    val loopBreakers = findLoopBreakers(annotatedPredIds, input)
    val cond = { pred: String =>
      input.findPredicate(pred).body.nonEmpty &&
      !loopBreakers(pred) &&
      annotatedPredIds(pred)
    }
    val rewrittenMethods = input.methods.map(rewriteMethod(_, input, cond))
    val rewrittenFunctions = input.functions.map(rewriteFunction(_, input, cond))
    val (inlinePreds, otherPreds) = input.predicates.partition(p => cond(p.name))
    val rewrittenPredicates = otherPreds.map(rewritePredicate(_, input, cond))
    val unfolding_helpers = inlinePreds.map(transformPredicate(_, input, cond))
    ViperStrategy.Slim({
      case program: Program =>
        program.copy(
          domains = input.domains ++ Seq(secondDomain),
          methods = rewrittenMethods,
          functions = rewrittenFunctions ++ unfolding_helpers,
          predicates = rewrittenPredicates
        )(program.pos, program.info, program.errT)
    }).execute[Program](input)
  }
}
