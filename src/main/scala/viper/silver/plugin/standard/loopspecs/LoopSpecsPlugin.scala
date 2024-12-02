package viper.silver.plugin.standard.loopspecs

import viper.silver.ast._
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
import viper.silver.parser.FastParserCompanion.{Pos, reservedKw}



class LoopSpecsPlugin (@unused reporter: viper.silver.reporter.Reporter,
                              @unused logger: ch.qos.logback.classic.Logger,
                              config: viper.silver.frontend.SilFrontendConfig,
                              fp: FastParser)  extends SilverPlugin with ParserPluginTemplate {

  import fp.{predAcc, ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmtBlock, stmt}
  import FastParserCompanion.{PositionParsing, reservedSym, whitespace, ExtendedParsing, Pos}


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
  /*def decreases[$: P]: P[PSpecification[PDecreasesKeyword.type]] =
    P((P(PDecreasesKeyword) ~ (decreasesWildcard | decreasesStar | decreasesTuple)) map (PSpecification.apply _).tupled).pos
  
  def decreasesTuple[$: P]: P[PDecreasesTuple] =
    P((exp.delimited(PSym.Comma) ~~~ condition.lw.?) map (PDecreasesTuple.apply _).tupled).pos
  def decreasesWildcard[$: P]: P[PDecreasesWildcard] = P((P(PWildcardSym) ~~~ condition.lw.?) map (PDecreasesWildcard.apply _).tupled).pos
  def decreasesStar[$: P]: P[PDecreasesStar] = P(P(PSym.Star) map (PDecreasesStar(_) _)).pos
  def condition[$: P]: P[(PReserved[PIfKeyword.type], PExp)] = 
    P(P(PIfKeyword) ~ exp)
*/

  def ghostBlock[$: P]: P[PGhostBlock] =
    P((reservedKw(PGhostKeyword) ~ ghostBody()) map {case (kw, body) => PGhostBlock(kw, body) _ }).pos

  def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos


  def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
    P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) => PBaseCaseBlock(kw, body) _ }).pos

  def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos

  // def old[$: P]: P[PKwOp.Old => Pos => POldExp] = P(oldLabel.brackets.? ~ exp.parens).map {
  //    case (lbl, g) => POldExp(_, lbl, g)
  //  }

  def loopspecs[$ : P]: P[PLoopSpecs] =

    // Parse the custom while loop
    P(
      (
      reservedKw(PKw.While) ~ parenthesizedExp ~~
      semiSeparated(precondition) ~~
      semiSeparated(postcondition) ~
      stmtBlock() ~
      ghostBlock.? ~
      baseCaseBlock.?
    ).map {
      case (whileKw, condExp, preSpec, postSpec, bodySeqn, maybeGhost,  maybeBaseCase) =>

        // PGrouped.Paren[PExp]
        PLoopSpecs(
          whileKw,
          condExp,
          preSpec,
          postSpec,
          bodySeqn,
          maybeGhost,
          maybeBaseCase
        )(_)
    }).pos

  def preExpr[$: P]: P[PPreExp] =
    P((reservedKw(PPreKeyword) ~ parenthesizedExp).map{
      case(preKw, exp) =>
        PPreExp(preKw, exp)(_)
    }).pos
  
  /*def whileStmt[$: P]: P[PKw.While => Pos => PWhile] =
    P((parenthesizedExp ~~ semiSeparated(invariant) ~ stmtBlock()) 
    map { case (cond, invs, body) => PWhile(_, cond, invs, body) })
    */

  /**
   * Add extensions to the parser
   */
  // So that it can parse our new while loop into a PLoopSpecs
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add 3 new keywords: ghost, basecase, pre
    ParserExtension.addNewKeywords(Set(PGhostKeyword, PBaseCaseKeyword, PPreKeyword))
    ParserExtension.addNewExpAtStart(preExpr(_))

    // Add new parser to the precondition
    //ParserExtension.addNewPreCondition(decreases(_))
    // Add new parser to the postcondition
    //ParserExtension.addNewPostCondition(decreases(_))
    // Add new parser to the invariants
    ParserExtension.addNewStmtAtStart(loopspecs(_))
    input
  }


  override def beforeVerify(input: Program): Program ={
    // For each loopspecs
    // Identify components of loop
    // Map entire loop to new code 1. inhalexhale 2. rec
    // Return input before ++ new code ++ input after



    //cond: Exp,
    //      pres: Seq[Exp],
    //      posts: Seq[Exp],
    //      body: Seqn,
    //      ghost: Option[Seqn],
    //      basecase


    //val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_refute_nondet$refutesInMethod", Bool)(r.pos)
    //          Seqn(Seq(
    //            If(nonDetLocalVarDecl.localVar,
    //              Seqn(Seq(
    //                Assert(exp)(r.pos, RefuteInfo(r)),
    //                Inhale(BoolLit(false)(r.pos))(r.pos, Synthesized)
    //              ), Seq())(r.pos),
    //              Seqn(Seq(), Seq())(r.pos))(r.pos)
    //          ),
    //            Seq(nonDetLocalVarDecl)
    //          )(r.pos)
    def mapLoopSpecs(ls : LoopSpecs): Node = {
      // Exhale all loop preconditions
      val check_pre: Seq[Stmt] =
        ls.pres.map(pre => Exhale(pre)())

      // Declare a non-deterministic Boolean variable
      val non_det =
        LocalVarDecl(s"__plugin_loopspecs_nondet", Bool)()

      // Common inhalations of preconditions
      val common_to_both_steps: Seq[Stmt] =
        ls.pres.map(pre => Inhale(pre)())

      // Inductive step statements
      val inductive_step: Seq[Stmt] =
        Seq(ls.body) ++
          ls.pres.map(pre => Exhale(pre)()) ++
          ls.posts.map(post => Inhale(post)()) ++
          ls.ghost.toSeq ++
          ls.posts.map(post => Exhale(post)())

      // Base step statements
      val base_step: Seq[Stmt] =
        Seq(ls.basecase) ++
          ls.posts.map(post => Exhale(post)())

      // Caller's postconditions
      val callers_post: Seq[Stmt] =
        ls.posts.map(post => Inhale(post)())

      // Construct the transformed sequence
      Seqn(
        check_pre ++ Seq(
          If(non_det.localVar,
            Seqn(Seq(
              While(TrueLit()(),
                Seq(),
                Seqn(
                  common_to_both_steps ++ Seq(
                    If(ls.cond,
                      Seqn(inductive_step,
                        Seq())(),
                      Seqn(base_step,
                        Seq())()
                    )()
                  ), Seq()
                )()
              )()
            ),
              Seq())(),
            Seqn(callers_post,
              Seq())()
          )()
        ),
        Seq(non_det)
      )()
    }



    val newProgram: Program = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        mapLoopSpecs(ls)

      case p: Program =>
        p
    }, Traverse.TopDown).execute(input) // TD or BU ??
    newProgram


    // Program(input.domains, input.fields, input.functions, input.predicates, transformedMethods, input.extensions)(input.pos, input.info, input.errT)
  }
}
