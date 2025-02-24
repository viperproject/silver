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

    import fp.{predAcc, annotatedStmt, stmtReservedKw, assign, funcApp, fieldAcc, idnuse, exp, ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmtBlock, stmt}
    import FastParserCompanion._
    import viper.silver.parser.PDelimited




    def ghostBlock[$: P]: P[PGhostBlock] =
      P((reservedKw(PGhostKeyword) ~ ghostBody()) map {case (kw, body) => PGhostBlock(kw, body) _ }).pos

    def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
      P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos


    def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
      P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) => PBaseCaseBlock(kw, body) _ }).pos

    def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
      P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos

//
//    // Define a new combinator to parse the while-loop body block.
//    // It expects an opening brace, then a sequence of (non-ghost) statements,
//    // then optionally a ghost block, and finally a closing brace.
//    def whileBodyBlock[$: P](allowDefine: Boolean = true): P[(PSeqn, Option[PGhostBlock])] = {
//      P(
//        (
//        // Parse the regular statements.
//        semiSeparated(stmt(allowDefine)) ~
//          // Parse an optional ghost block (which is expected to come last if present).
//          ghostBlock.?
//        ).braces map
//          {
//            case wholeBody :  PGrouped[PSym.Brace, (PDelimited[PStmt, Option[PReserved[PSym.Semi.type]]], Option[PGhostBlock])] =>
//              val (stmts, ghostOpt) = wholeBody.inner
//
//              (stmts, ghostOpt)
//      }
//      ).pos
//
//    }//todo add support for ghost inside body ==> change all tests

//    // Now, update loopspecs to use whileBodyBlock instead of stmtBlock().
//    def loopspecs[$: P]: P[PLoopSpecs] = P(
//      // Parse the while header (keyword, condition, preconditions, postconditions)
//      reservedKw(PKw.While) ~ parenthesizedExp ~~
//        semiSeparated(precondition) ~~ semiSeparated(postcondition) ~~~
//        // Parse the while-loop body using our custom combinator.
//        whileBodyBlock() ~
//        // Parse an optional basecase block (which lies outside the while-loop's braces).
//        baseCaseBlock.?
//    ).map {
//      // Note: preSpec and postSpec come from semiSeparated(precondition) and semiSeparated(postcondition)
//      case (whileKw, condExp, preSpec, postSpec, (bodySeqn, maybeGhost), maybeBaseCase) =>
//        // Construct the loop spec AST node with the extracted ghost block.
//        PLoopSpecs(
//          whileKw,
//          condExp,
//          preSpec,
//          postSpec,
//          bodySeqn,
//          maybeGhost,
//          maybeBaseCase
//        )(_)
//    }.pos

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


//    def loopspecs[$: P]: P[PLoopSpecs] = P(
//      // Parse the while loop header and body
//      reservedKw(PKw.While) ~ parenthesizedExp ~~
//        semiSeparated(precondition) ~~ semiSeparated(postcondition) ~~~
//        stmtBlock().lw ~
//        baseCaseBlock.?
//    ).map {
//      case (whileKw, condExp, preSpec, postSpec, bodySeqn, maybeBaseCase) =>
//        // Assume bodySeqn: PSeqn contains a Seq[PStmt] in its 'stmts' field.
//        // Partition the statements into ghost blocks and non-ghost statements.
//        val (ghostStmts, nonGhostStmts) = bodySeqn.ss.partition {
//          case _: PGhostBlock => true
//          case _              => false
//        }
//        // Since we assume at most one ghost block, take the first ghost block if it exists.
//        val maybeGhost: Option[PGhostBlock] = ghostStmts.headOption.collect {
//          case gb: PGhostBlock => gb
//        }
//        // Reassemble the loop body without the ghost block.
//        val newBodySeqn: PSeqn = PSeqn(nonGhostStmts)
//
//        // Construct the loop specification with the ghost and base-case blocks separately.
//        PLoopSpecs(
//          whileKw,
//          condExp,
//          preSpec,
//          postSpec,
//          newBodySeqn,
//          maybeGhost,
//          maybeBaseCase
//        )(_)
//    }.pos


    def loopspecs2[$ : P]: P[PLoopSpecs] =

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
    override def beforeVerify(input: Program): Program ={
        val ls = new LoopSpecsInhaleExhale(this, input)
        ls.beforeVerify()
    }


    override def reportError(error: AbstractError): Unit = {
      super.reportError(error)
    }
  }
