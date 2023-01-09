package viper.silver.plugin.standard.permprime

import fastparse._
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser._
import viper.silver.plugin.SilverPlugin

import scala.annotation.unused

case class PMethodCallPrime(
  targets: Seq[PIdnUse],
  method: PIdnUse,
  args: Seq[PExp]
)(val pos: (Position, Position)) extends PStmt with PExtender {

  override val getSubnodes: Seq[PNode] = targets ++ Seq(method) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    println("[PMethodCallPrime] Enter typecheck")
    targets.foreach(t.checkTopTyped(_, None))
    // t.checkTopTyped(method, None)
    args.foreach(t.checkTopTyped(_, None))
    // TODO: Copy other parts from PMethodCall
    println("[PMethodCallPrime] Exit typecheck")
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
                @unused config: viper.silver.frontend.SilFrontendConfig,
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
    var curLabel = 0
    def mkLabel(pos: (Position, Position)): PLabel = {
      curLabel += 1
      PLabel(PIdnDef("pp" + curLabel)(pos), Nil)(pos)
    }
    val result: PProgram = StrategyBuilder.Slim[PNode] {
      case pcall: PMethodCallPrime =>
        val initLabel = mkLabel(pcall.pos)
        val method = input.methods.find(_.idndef.name == pcall.method.name).get
        val stmts = {
          List(initLabel) ++
          method.pres.map { pre =>

            val inlined: PExp = StrategyBuilder.Slim[PNode] {
              case ident: PIdnUse =>
                val argIdx = method.formalArgs.indexWhere(_.idndef.name == ident.name)
                if(argIdx >= 0) {
                  pcall.args(argIdx)
                } else {
                  ident
                }
            }.execute(pre)

            val repPP: PExp = StrategyBuilder.Slim[PNode] {
              case pp: PPermPrime =>
                val curPerm = PCurPerm(pp.res)(pp.pos)
                val outsidePerm = PLabelledOld(
                  PIdnUse(initLabel.idndef.name)(pp.pos),
                  curPerm
                )(pp.pos)
                PBinExp(
                  outsidePerm,
                  "-",
                  curPerm
                )(pp.pos)
            }.execute(inlined)

            PExhale(repPP)(pcall.pos)
          } ++
          method.posts.map { post =>
            PInhale(post)(pcall.pos)
          }
        }
        PSeqn(stmts)(pcall.pos)
      case method: PMethod =>
        method.copy(
          pres = method.pres.filterNot { c =>
              (Visitor.find(c, (e: PNode) => e.subnodes) {
                case _: PPermPrime => true
              }).isDefined
            }
        )(method.pos)
    }.execute(input)
    println("[PermPrime] exit beforeTranslate")
    result
  }

  override def beforeParse(input: String, isImported: Boolean): String = {
    println("[PermPrime] enter beforeParse")
    ParserExtension.addNewKeywords(Set(PermPrimeKeyword, CallPrimeKeyword))
    ParserExtension.addNewStmtAtStart(callPrimeStmt(_))
    ParserExtension.addNewExpAtStart(permPrimeExp(_))
    println("[PermPrime] exit beforeParse")
    input
  }
}
