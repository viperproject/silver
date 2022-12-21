package viper.silver.plugin.standard.permprime

import fastparse._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.ast.{ErrorTrafo, Exp, ExtensionStmt, Info, LocalVar, Node, Position, Program, Seqn, Stmt}
import viper.silver.parser.{FastParser, PExp, PIdnUse, PSeqn, PStmt}
import viper.silver.plugin.SilverPlugin
import viper.silver.parser.FastParserCompanion.whitespace

case class PMethodCallPrime(
  targets: Seq[PIdnUse],
  method: PIdnUse,
  args: Seq[PExp]
)(val pos: (Position, Position)) extends PStmt

case class MethodCallPrime(
  methodName: String,
  args: Seq[Exp],
  targets: Seq[LocalVar]
)(val pos: Position, val info: Info, val errT: ErrorTrafo) extends ExtensionStmt {
  override def extensionSubnodes: Seq[Node] = args ++ targets

  override def prettyPrint: PrettyPrintPrimitives#Cont = ???
}

class PermPrimePlugin(fp: FastParser) extends SilverPlugin {

  import fp.{FP, ParserExtension, exp, idnuse, parens}

  private val PermPrimeKeyword: String = "perm'"
  private val CallPrimeKeyword: String = "call'"

  def callPrimeStmt[_: P]: P[PMethodCallPrime] = FP((idnuse.rep(sep = ",") ~ ":=").? ~ CallPrimeKeyword ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (pos, (None, method, args)) =>
      PMethodCallPrime(Nil, method, args)(pos)
    case (pos, (Some(targets), method, args)) =>
      PMethodCallPrime(targets, method, args)(pos)
  }

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set(PermPrimeKeyword, CallPrimeKeyword))
    ParserExtension.addNewStmtAtEnd(callPrimeStmt(_))
    input
  }

  private def inlinePC(prime: MethodCallPrime, program: Program): List[Stmt] = {
    program.methods.find(method => prime.methodName == method.name)
    Nil
  }

  override def beforeVerify(input: Program): Program = {
    val newProgram: Program = StrategyBuilder.Slim[Node]({
      case seqn@Seqn(ss, decls) =>
        Seqn(
          ss.flatMap {
            case pc: MethodCallPrime => inlinePC(pc, input)
            case other => List(other)
          },
          decls
        )(seqn.pos)
    }, Traverse.BottomUp).execute(input)

    newProgram

  }

}
