package viper.silver.plugin.standard.permprime

import fastparse._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.ast.{CurrentPerm, ErrorTrafo, Exp, ExtensionExp, ExtensionStmt, Info, LocalVar, MethodCall, NoInfo, NoPosition, NoTrafos, Node, Perm, PermExp, Position, Program, ResourceAccess, Seqn, Stmt, Type}
import viper.silver.parser.{FastParser, NameAnalyser, PCurPerm, PExp, PExtender, PIdnUse, PMethod, PNode, PProgram, PResourceAccess, PSeqn, PStmt, PTypeSubstitution, Translator, TypeChecker}
import viper.silver.plugin.SilverPlugin
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.verifier.VerificationResult

import scala.annotation.unused

case class PMethodCallPrime(
  targets: Seq[PIdnUse],
  method: PIdnUse,
  args: Seq[PExp]
)(val pos: (Position, Position)) extends PStmt with PExtender {

  override val getSubnodes: Seq[PNode] = targets ++ Seq(method) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Copy from PMethodCall
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    // TODO: Real implementation
    val ts = (targets map t.exp).asInstanceOf[Seq[LocalVar]]
    MethodCall(t.findMethod(method), args map t.exp, ts)(this.pos._1 /* TODO: Is this right? */)
  }
}
case class PPermPrime (res: PResourceAccess)(val pos: (Position, Position)) extends PExtender with PExp {

  override def translateExp(t: Translator): Exp = {
    t.exp(PCurPerm(res)(pos))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(res, None)
    None
  }
  override def getSubnodes(): Seq[PNode] = List(res)
  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = ???

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
}
class PermPrimePlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin {

  import fp.{FP, ParserExtension, exp, idnuse, parens, resAcc}

  private val PermPrimeKeyword: String = "perm'"
  private val CallPrimeKeyword: String = "call"

  def callPrimeStmt[_: P]: P[PMethodCallPrime] = FP((idnuse.rep(sep = ",") ~ ":=").? ~ CallPrimeKeyword ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (pos, (None, method, args)) =>
      PMethodCallPrime(Nil, method, args)(pos)
    case (pos, (Some(targets), method, args)) =>
      PMethodCallPrime(targets, method, args)(pos)
  }

  def permPrimeExp[_: P]: P[PPermPrime] = {
    FP(PermPrimeKeyword ~ parens(resAcc)).map{
      case (pos, r) => PPermPrime(r)(pos)
    }
  }

  override def beforeTranslate(input: PProgram): PProgram = {
    println("[PermPrime] enter beforeTranslate")
    StrategyBuilder.Slim[PNode] {
      case method: PMethod =>
        method.copy(
          pres = method.pres.filterNot { c =>
              (Visitor.find(c, (e: PNode) => e.subnodes) {
                case _: PPermPrime => true
              }).isDefined
            }
        )(method.pos)
    }.execute(input)
  }

  override def beforeParse(input: String, isImported: Boolean): String = {
    println("[PermPrime] enter beforeParse")
    ParserExtension.addNewKeywords(Set(PermPrimeKeyword, CallPrimeKeyword))
    ParserExtension.addNewStmtAtEnd(callPrimeStmt(_))
    ParserExtension.addNewExpAtStart(permPrimeExp(_))
    input
  }
}
