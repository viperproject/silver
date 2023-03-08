package viper.silver.plugin.standard.inline

import ch.qos.logback.classic.Logger
import fastparse._
import viper.silver.ast.Program
import viper.silver.frontend.{DefaultIPS, InlinePredicateStrategy, SilFrontendConfig}
import viper.silver.parser._
import viper.silver.plugin.{IOAwarePlugin, ParserPluginTemplate, SilverPlugin}
import viper.silver.reporter.{Entity, Reporter}
import viper.silver.verifier.{AbstractVerificationError, Failure, Success, VerificationResult}

import scala.annotation.unused

class InlinePredicatePlugin(val reporter: Reporter, val logger: Logger, val cmdArgs: SilFrontendConfig, val fp: FastParser)
  extends SilverPlugin with ParserPluginTemplate with IOAwarePlugin  with InlineRewrite with InlineErrorChecker {
  import fp._
  val inlineLevel: Int = if (cmdArgs == null) 1 else cmdArgs.inlinePluginLevel()
  val inlineStat: InlinePredicateStrategy = if (cmdArgs == null) DefaultIPS else cmdArgs.inlinePredicateStrategy()

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

  def targetPredIds(input: Program): Set[String] = {
    inlineLevel match {
      case 0 => Set()
      case 1 => this.annotatedPredIds
      case 2 => input.predicates.filter(_.body.isDefined).map(_.name).toSet
    }
  }

  override def beforeVerify(input: Program): Program = {
    val annotatedPredIds = this.targetPredIds(input)
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
    val res = rewriteProgram(input.copy(predicates = otherPreds)(input.pos, input.info, input.errT), inlinePreds, inlineStat)
    res
  }

  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult =
    translateVerificationResult(input)

  override def mapVerificationResult(@unused program: Program, input: VerificationResult): VerificationResult =
    translateVerificationResult(input)

  // Transform all errors
  private def translateVerificationResult(input: VerificationResult): VerificationResult = {
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
