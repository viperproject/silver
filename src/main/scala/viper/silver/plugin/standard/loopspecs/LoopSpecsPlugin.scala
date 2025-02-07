  package viper.silver.plugin.standard.loopspecs

  import viper.silver.ast.{LocalVarAssign, _}
  import viper.silver.ast.utility.ViperStrategy
  import viper.silver.ast.utility.rewriter.Traverse
  import viper.silver.parser._
  import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
  import viper.silver.verifier.{AbstractError, ConsistencyError, Failure, Success, VerificationResult}
  import viper.silver.verifier.errors.{ExhaleFailed, InhaleFailed, PreconditionInAppFalse}
  import fastparse._
  import viper.silver.ast.pretty.PrettyPrintPrimitives
  import viper.silver.reporter.Entity

  import scala.annotation.unused
  import scala.collection.immutable.ListMap
  import viper.silver.parser.FastParserCompanion.{Pos, reservedKw}




  class LoopSpecsPlugin (@unused reporter: viper.silver.reporter.Reporter,
                                @unused logger: ch.qos.logback.classic.Logger,
                                config: viper.silver.frontend.SilFrontendConfig,
                                fp: FastParser)  extends SilverPlugin with ParserPluginTemplate {

    import fp.{predAcc, funcApp, fieldAcc, idnuse, exp, ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmtBlock, stmt}
    import FastParserCompanion._


    private def deactivated: Boolean = config != null && config.disableTerminationPlugin.toOption.getOrElse(false)

    //TODO: Add some variable in config to choose which version of desugaring: inex, rec


    def ghostBlock[$: P]: P[PGhostBlock] =
      P((reservedKw(PGhostKeyword) ~ ghostBody()) map {case (kw, body) => PGhostBlock(kw, body) _ }).pos

    def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
      P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos


    def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
      P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) => PBaseCaseBlock(kw, body) _ }).pos

    def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
      P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos



    def loopspecs[$ : P]: P[PLoopSpecs] =

      // Parse the custom while loop
      P(
        (
        reservedKw(PKw.While) ~ parenthesizedExp ~~
        semiSeparated(precondition) ~~
        semiSeparated(postcondition) ~~~
        stmtBlock().lw ~
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


//    def loopspecs_other_syntax[$ : P]: P[PLoopSpecs] =
//
//      // Parse the custom while loop
//      P(
//        (
//          reservedKw(PKw.While) ~ parenthesizedExp ~~
//            semiSeparated(precondition) ~~
//            semiSeparated(postcondition) ~~~
//            stmtBlock().lw ~
//            baseCaseBlock.? ~
//            ghostBlock.?
//          ).map {
//          case (whileKw, condExp, preSpec, postSpec, bodySeqn, maybeGhost,  maybeBaseCase) =>
//
//            // PGrouped.Paren[PExp]
//            PLoopSpecs(
//              whileKw,
//              condExp,
//              preSpec,
//              postSpec,
//              bodySeqn,
//              maybeBaseCase,
//              maybeGhost
//            )(_)
//        }).pos

    def preExpr[$: P]: P[PPreExp] =
      P((reservedKw(PPreKeyword) ~ parenthesizedExp).map{
        case(preKw, exp) =>
          PPreExp(preKw, exp)(_)
      }).pos

    def assignTarget[$: P]: P[PExp] = P(fieldAcc | funcApp | idnuse | preExpr)


    //Same as assign but also considers pres to be able to appear as targets of an assignment
//    def preAssign[$: P]: P[PPreAssign] = P(
//      (assignTarget.delimited(PSym.Comma, min = 1) ~~~ (P(PSymOp.Assign).map(Some(_)) ~ exp).lw.?)
//        filter (a => a._2.isDefined || (a._1.length == 1 && (a._1.head.isInstanceOf[PIdnUse] || a._1.head.isInstanceOf[PCall])))
//        map (a => if (a._2.isDefined) PPreAssign(a._1, a._2.get._1, a._2.get._2) _
//      else PPreAssign(PDelimited.empty, None, a._1.head) _)
//    ).pos


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
      //ParserExtension.addNewStmtAtStart(loopspecs_other_syntax(_))
      //ParserExtension.addNewStmtAtStart(preAssign(_))
      input
    }

    //Well-definedness
    // Reject pre(.) if not in post/ghost/bc (manual checking in befVerify()) ==> add test case DONE
    // ALso this is taken care of indircetly by Viper as it will complain about what to do with the pre: don't know how readable
    // the error will be though.
    // ExpectedOutput(consistency.error) as there's no reason
    //TODO: transform final englobing inhale error into post error (override def) ??
    // rn it says cant prove englobing postcond, maybe it should say "basecase not strong enough"

    //TODO: More positive big examples
    override def beforeVerify(input: Program): Program ={
        val ls = new LoopSpecsInhaleExhale(this, input)
        ls.beforeVerify()
    }


    override def reportError(error: AbstractError): Unit = {
      super.reportError(error)
    }
  }
