package silAST.methods.implementations

import scala.collection.Seq
import collection.mutable.ListBuffer
import silAST.source.SourceLocation
import silAST.methods.Scope
import silAST.programs.symbols.ProgramVariable
import silAST.expressions.terms.PTerm
import silAST.expressions.PExpression

final class BasicBlock private[silAST]
  (
    val cfg : ControlFlowGraph,
    val scope: Scope,
    val label: String,
    val factory: BasicBlockFactory
  )
  (val sourceLocation: SourceLocation)
  extends Block
{

  def statements: Seq[Statement] = pStatements.result()
  override val implementation = cfg.implementation

  private val pStatements = new ListBuffer[Statement]

  private[silAST] def appendStatement(s: Statement) = {
    require(!(pStatements contains s))
    pStatements += s
  }

  override def readVariables : Set[ProgramVariable] =
    (for (s <- statements) yield s.readVariables ).flatten.toSet[ProgramVariable] union
    (for (s <- successors) yield s.condition.programVariables).flatten.toSet
  override def writtenVariables : Set[ProgramVariable] = (for (s <- statements) yield s.writtenVariables ).flatten.toSet

  /////////////////////////////////////////////////////////////////////////////////////////
  override def equals(other: Any): Boolean = {
    other match {
      case b: BasicBlock => b eq this
      case _ => false
    }
  }

  override def hashCode(): Int = statements.hashCode()


  override def toString =
    "\t" + label + ":{\n" +
      (if (!statements.isEmpty) statements.mkString("\t\t", "\n\t\t", "\n") else "") +
      controlFlowToString +
      "\t}\n"

}
