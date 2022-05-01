package viper.silver.plugin.standard.inline

import fastparse._
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
    val (loopBreakers, topoOrder) = findLoopBreakersTopo(annotatedPredIds, input)
    val cond = { pred: String =>
      input.findPredicate(pred).body.nonEmpty &&
      !loopBreakers(pred) &&
      annotatedPredIds(pred)
    }
    val (inlinePredsUnordered, otherPreds) = input.predicates.partition(p => cond(p.name))
    val inlinePreds = topoOrder.map(name => inlinePredsUnordered.find(_.name == name).get)
    if(inlinePreds.isEmpty) {
      return input
    }
    rewriteProgram(input.copy(predicates = otherPreds)(input.pos, input.info, input.errT), inlinePreds)
  }
}
