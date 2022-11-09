package viper.silver.plugin.standard.reasoning


import fastparse.P
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PLocalVarDecl}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.AssertFailed

import scala.annotation.unused

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, keyword, exp, ParserExtension, idndef, typ, trigger}

  /** Parser for existential elimination statements. */
  def existential_elim[_: P]: P[PExistentialElim] = {
    //FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ exp).map{ case (pos, (varList, e)) => PExistentialElim(varList, e)(pos) }
    // version with local var decl
    //FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ exp).map{ case (pos, (varList, e)) => PExistentialElim(varList.map { case (id,typ) => PLocalVarDecl(id,typ,None)(e.pos)}, e)(pos) }

    //version without local var decl and with triggers
    FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ trigger.rep ~/ exp).map { case (pos, (varList, t, e)) => PExistentialElim(varList.map { case (id, typ) => (id.name, typ) }, t, e)(pos) }

  }
  // trigger after where (Seq(PTrigger))


  /** Add existential elimination to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    scala.Console.println("entered beforeParse: " + input)
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String]("obtain", "where"))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(existential_elim(_))
    input
  }


  override def beforeVerify(input: Program): Program = {
    scala.Console.println("entered beforeVerify: "+ input.info.toString)
    ViperStrategy.Slim({
      case e@ExistentialElim(v, exp) => { // e = ExistentialElim(vardecl, exp)
        Seqn(
          Seq(
            // version with local var decl
            Assert(Exists(v, Seq(), exp)(e.pos, ReasoningInfo))(e.pos))

            // version without local var decl
            //Assert(Exists(v.map{case (id,typ) => LocalVarDecl(id,typ)(exp.pos)}, Seq(), exp)(e.pos, ReasoningInfo))(e.pos))
          ++
          // version with local var decl
          v.map { case variable => LocalVarDeclStmt(variable)(variable.pos) } //list of variables

          // version without local var decl
          //v.map { case variable => LocalVarDeclStmt(LocalVarDecl(variable._1,variable._2)(exp.pos))(exp.pos) } //list of variables

          ++
          Seq(
            Inhale(exp)(e.pos)
          ),
          Seq()
        )(e.pos)
      }
    }, Traverse.TopDown).execute(input)
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    val errors: Seq[AbstractError] = (input match {
      case Success => Seq()
      case Failure(errors) => {
        errors.map {
          case AssertFailed(a, err_reason, c) if a.info == ReasoningInfo => {
            ExistentialElimFailed(a, err_reason, c)
          }
        }
      }
    })
    if (errors.length == 0) Success
    else Failure(errors)
  }
}

