package viper.silver.plugin.standard.loopspecs

import viper.silver.ast._
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

/**
 * The `LoopSpecsPlugin` extends Viper Silver with additional syntax and parsing logic
 * for loops that have custom specifications:
 *   - `ghost { ... }` blocks,
 *   - `basecase { ... }` blocks,
 *   - `pre(...)` expressions.
 *
 * This class hooks into the parser pipeline and transforms the resulting AST before verification.
 * The main goal is to capture loop invariants (in pre- and postconditions) and extra ghost/basecase
 * code within the usual Silver AST for further processing (e.g., translation to recursion).
 */
class LoopSpecsPlugin(
                       @unused reporter: viper.silver.reporter.Reporter,
                       @unused logger: ch.qos.logback.classic.Logger,
                       config: viper.silver.frontend.SilFrontendConfig,
                       fp: FastParser
                     ) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmt}
  import FastParserCompanion._
  import viper.silver.parser.PDelimited
  import viper.silver.parser.PKw.InvSpec

  /**
   * Parses a `ghost` block of the form `ghost { ... }`, returning a `PGhostBlock`.
   * A `ghost` block can contain an arbitrary sequence of statements, stored as a `PSeqn`.
   */
  def ghostBlock[$: P]: P[PGhostBlock] =
    P((reservedKw(PGhostKeyword) ~ ghostBody()) map { case (kw, body) =>
      PGhostBlock(kw, body) _
    }).pos

  /**
   * Parses the inner statements of a `ghost` block, enclosed in braces `{ ... }`.
   */
  def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces.map(PSeqn.apply)).pos

  /**
   * Parses a `basecase` block of the form `basecase { ... }`, returning a `PBaseCaseBlock`.
   * This block similarly contains a sequence of statements.
   */
  def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
    P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) =>
      PBaseCaseBlock(kw, body) _
    }).pos

  /**
   * Parses the inner statements of a `basecase` block, enclosed in braces `{ ... }`.
   */
  def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces.map(PSeqn.apply)).pos

  /**
   * Custom parser for the body of a `while` loop that might contain:
   *   - Normal statements (in braces),
   *   - An optional `ghost { ... }` block.
   *
   * Returns a `PWhileBodyBlock` with both the body statements and the optional ghost block.
   */
  def whileBodyBlock[$: P](allowDefine: Boolean = true, forceGhost : Boolean = false): P[PWhileBodyBlock] = {
    if(forceGhost){
      P(
        (semiSeparated(stmt(allowDefine)) ~ ghostBlock).braces.map { wrapped =>
          val (stmtsDelimited, ghostOpt) = wrapped.inner
          val first = stmtsDelimited.first
          val inner = stmtsDelimited.inner.map { case (_, stmt) => stmt }

          // Combine statements into a single PSeqn node.
          val stmtsSeqn = PSeqn(PDelimited.impliedBlock(first.toSeq ++ inner))(wrapped.pos)

          // Build a single AST node with the body + optional ghost block.
          PWhileBodyBlock(
            body  = stmtsSeqn,
            ghost = Some(ghostOpt)
          )(wrapped.pos)
        }
      )
    }else{
      P(
        (semiSeparated(stmt(allowDefine)) ~ ghostBlock.?).braces.map { wrapped =>
          val (stmtsDelimited, ghostOpt) = wrapped.inner
          val first = stmtsDelimited.first
          val inner = stmtsDelimited.inner.map { case (_, stmt) => stmt }

          // Combine statements into a single PSeqn node.
          val stmtsSeqn = PSeqn(PDelimited.impliedBlock(first.toSeq ++ inner))(wrapped.pos)

          // Build a single AST node with the body + optional ghost block.
          PWhileBodyBlock(
            body  = stmtsSeqn,
            ghost = ghostOpt
          )(wrapped.pos)
        }
      )
    }

  }

  /**
   * Grammar rule for a custom annotated `while` loop, producing a `PLoopSpecs` node:
   * {{{
   *   while (condition)
   *     requires ...
   *     ensures ...
   *   {
   *     <body statements>    // optional
   *     ghost { ... }        // optional
   *   }
   *   basecase { ... }       // optional block following the loop
   * }}}
   */
    //todo: have this not conflict with normal while loops
    // test this with all tests
  def loopspecs[$: P]: P[PLoopSpecs] = P(
//    (reservedKw(PKw.While)
//      ~ parenthesizedExp ~~
//      semiSeparatedMinOne(precondition) ~~ //>= 1 precond
//      semiSeparated(postcondition) ~
//      whileBodyBlock() ~
//      baseCaseBlock.?) |
//
//      (reservedKw(PKw.While)
//        ~ parenthesizedExp ~~
//        semiSeparated(precondition) ~~
//        semiSeparatedMinOne(postcondition) ~ // >= 1 postcond
//        whileBodyBlock() ~
//        baseCaseBlock.?) |
//
//      (reservedKw(PKw.While)
//        ~ parenthesizedExp ~~
//        semiSeparated(precondition) ~~
//        semiSeparated(postcondition) ~
//        whileBodyBlock(forceGhost = true) ~ //or ghost block
//        baseCaseBlock.?) |

      NoCut(reservedKw(PKw.While)
        ~ parenthesizedExp ~~
        semiSeparated(precondition) ~~
        semiSeparated(postcondition) ~
        whileBodyBlock() ~
        baseCaseBlock.?)
  )
    .filter(f =>
  {
    val (_, _, preSpec, postSpec, whileBodyBlock, maybeBaseCase) = f

    preSpec.length > 0 || postSpec.length > 0 || whileBodyBlock.ghost.nonEmpty || maybeBaseCase.nonEmpty
  })
    .map {
    case (whileKw, condExp, preSpec, postSpec, whileBodyBlock, maybeBaseCase)
      //if preSpec.length > 0 || postSpec.length > 0 || whileBodyBlock.ghost.nonEmpty || maybeBaseCase.nonEmpty
      =>
      PLoopSpecs(
        whileKw,
        condExp,
        preSpec,
        postSpec,
        whileBodyBlock.body,
        whileBodyBlock.ghost,
        maybeBaseCase
      )(_)
    //case (whileKw, condExp, preSpec, postSpec, whileBodyBlock, maybeBaseCase) =>
      //PWhile(whileKw, condExp, PDelimited(None, Seq(), None)(NoPosition, NoPosition), whileBodyBlock.body)(_)
  }.pos

  /**
   * Parser for a `pre(...)` expression, wrapping an existing expression
   * to indicate it's referencing the pre-iteration state of a variable or object.
   */
  def preExpr[$: P]: P[PPreExp] =
    P((reservedKw(PPreKeyword) ~ parenthesizedExp).map {
      case(preKw, exp) =>
        PPreExp(preKw, exp)(_)
    }).pos

  /**
   * Adds the new keywords `ghost`, `basecase`, and `pre` to the parser
   * and registers our custom parser extensions for them.
   * Called before the parsing of the input begins.
   */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Declare new keywords
    ParserExtension.addNewKeywords(Set(PGhostKeyword, PBaseCaseKeyword, PPreKeyword))
    // Register custom grammar rules
    ParserExtension.addNewExpAtStart(preExpr(_))
    ParserExtension.addNewStmtAtStart(loopspecs(_))
    input
  }

  /**
   * Called after parsing but before verification:
   * we transform the program by expanding `while` loops with specs into
   * additional statements/instructions (exhales/inhales, etc.).
   * @param input The parsed program AST.
   * @return The transformed AST ready for verification.
   */
  override def beforeVerify(input: Program): Program = {
    val ls = new LoopSpecsInhaleExhale(this, input)
    ls.beforeVerify()
  }

  /**
   * Custom error reporting, if needed.
   * This plugin can produce specialized consistency checks or warnings.
   */
  override def reportError(error: AbstractError): Unit = {
    super.reportError(error)
  }
}
