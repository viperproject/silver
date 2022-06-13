package viper.silver.plugin.standard.inline

import fastparse._
import viper.silver.ast.Program
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractVerificationError, Failure, Success, VerificationResult}

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate
  with InlineRewrite
  with InlineErrorChecker {

  private[this] val InlinePredicateKeyword = "inline"

  private var annotatedPredIds: Set[String] = Set()

  // like viper.silver.parser.FastParser.predicateDecl but the body can't be empty
  def predicateDeclBody[_: P]: P[PPredicate] = FP(keyword("predicate") ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ "{" ~ exp ~ "}").map {
    case (_, (a, b, c)) =>
      PPredicate(a, b, Some(c))(a.pos)
  }


  def inlinePredicate[_: P]: P[PInlinePredicate] = FP(InlinePredicateKeyword ~/ predicateDeclBody).map{ case (_, p) => PInlinePredicate(p)}

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
    if(annotatedPredIds.isEmpty) {
      return input
    }
    val (loopBreakers, topoOrder) = findLoopBreakersTopo(annotatedPredIds, input)
    val cond = { pred: String =>
      input.findPredicate(pred).body.nonEmpty &&
      !loopBreakers(pred) &&
      annotatedPredIds(pred)
    }
    val (inlinePredsUnordered, otherPreds) = input.predicates.partition(p => cond(p.name))
    val inlinePreds = topoOrder.map(name => inlinePredsUnordered.find(_.name == name).get)
    val res = rewriteProgram(input.copy(predicates = otherPreds)(input.pos, input.info, input.errT), inlinePreds, assertFolds = true)
    print(res)
    res
  }

  // Transform all errors
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => input
      case Failure(errors) =>
        Failure(errors.map {
          case e: AbstractVerificationError => e.transformedError()
          case oth => oth
        })
    }
  }
}
