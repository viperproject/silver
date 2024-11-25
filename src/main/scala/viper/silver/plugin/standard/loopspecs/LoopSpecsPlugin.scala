package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{Domain, DomainType, ErrTrafo, FuncApp, Function, Position, PredicateAccess, PredicateAccessPredicate, Program, WildcardPerm}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.PreconditionInAppFalse
import fastparse._
import viper.silver.reporter.Entity

import scala.annotation.unused
import scala.collection.immutable.ListMap
import viper.silver.parser.FastParserCompanion.reservedKw

class LoopSpecsPlugin (@unused reporter: viper.silver.reporter.Reporter,
                              @unused logger: ch.qos.logback.classic.Logger,
                              config: viper.silver.frontend.SilFrontendConfig,
                              fp: FastParser)  extends SilverPlugin with ParserPluginTemplate {

  import fp.{predAcc, ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmtBlock, exp, stmt}
  import FastParserCompanion.{PositionParsing, reservedSym, whitespace, ExtendedParsing}


  private def deactivated: Boolean = config != null && config.disableTerminationPlugin.toOption.getOrElse(false)

  //TODO: Add some variable in config to choose which version of desugaring: inhaleexhale, rec


  //private var decreasesClauses: Seq[PDecreasesClause] = Seq.empty

  /**
   * Parser for decreases clauses with following possibilities.
   *
   * decreases (exp (, exp)*)? (if exp)?
   * or
   * decreases _ (if exp)?
   * or
   * decreases *
   */
  def decreases[$: P]: P[PSpecification[PDecreasesKeyword.type]] =
    P((P(PDecreasesKeyword) ~ (decreasesWildcard | decreasesStar | decreasesTuple)) map (PSpecification.apply _).tupled).pos
  
  def decreasesTuple[$: P]: P[PDecreasesTuple] =
    P((exp.delimited(PSym.Comma) ~~~ condition.lw.?) map (PDecreasesTuple.apply _).tupled).pos
  def decreasesWildcard[$: P]: P[PDecreasesWildcard] = P((P(PWildcardSym) ~~~ condition.lw.?) map (PDecreasesWildcard.apply _).tupled).pos
  def decreasesStar[$: P]: P[PDecreasesStar] = P(P(PSym.Star) map (PDecreasesStar(_) _)).pos
  def condition[$: P]: P[(PReserved[PIfKeyword.type], PExp)] = 
    P(P(PIfKeyword) ~ exp)

  //TODO: fix the pos problem.
  // 1. not using the right position for ghost and base case.
  // 2. using _ multiple times refers to subsequent args

  def ghostBlock[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos

  def baseCaseBlock[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos
  //TODO: Extract ghost and base case rules
  def loopspecs[$ : P]: P[PLoopSpecs] =

    // Parse the custom while loop
    P(
      (
      reservedKw(PKw.While) ~ parenthesizedExp ~~
      semiSeparated(precondition) ~~
      semiSeparated(postcondition) ~
      stmtBlock() ~
      (reservedKw(PGhostKeyword) ~ ghostBlock()).? ~
      (reservedKw(PBaseCaseKeyword) ~ baseCaseBlock()).?
    ).map {
      case (whileKw, condExp, preSpec, postSpec, bodySeqn, maybeGhost, maybeBaseCase) =>

        PLoopSpecs(
          whileKw,
          PGrouped(PReserved(PSym.LParen), 
                  condExp, 
                  PReserved(PSym.RParen)),
          preSpec,
          postSpec,
          bodySeqn,
          maybeGhost,
          maybeBaseCase
        )(_)
    }).pos

  
  def whileStmt[$: P]: P[PKw.While => Pos => PWhile] =
    P((parenthesizedExp ~~ semiSeparated(invariant) ~ stmtBlock()) 
    map { case (cond, invs, body) => PWhile(_, cond, invs, body) })
                              

  /**
   * Add extensions to the parser
   */
  // So that it can parse our new while loop into a PLoopSpecs
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add 3 new keywords: ghost, basecase, pre
    ParserExtension.addNewKeywords(Set(PGhostKeyword, PBaseCaseKeyword, PPreKeyword))

    // Add new parser to the precondition
    //ParserExtension.addNewPreCondition(decreases(_))
    // Add new parser to the postcondition
    //ParserExtension.addNewPostCondition(decreases(_))
    // Add new parser to the invariants
    ParserExtension.addNewStmtAtStart(loopspecs(_))
    input
  }
}
