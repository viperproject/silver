package silAST.methods.implementations

import scala.collection.{Seq, Set}
import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.SourceLocation
import silAST.programs.symbols.ProgramVariable
import silAST.expressions.ExpressionFactory

final class BasicBlock private[silAST](
                                        sl: SourceLocation,
                                        val label: String
                                        ) extends ASTNode(sl) {
  private[implementations] def addPredecessor(edge: CFGEdge) {
    require(edge.target == this)
    pPredecessors += edge
  }

  private[implementations] def addSuccessor(edge: CFGEdge) {
    require(edge.source == this)
    pSuccessors += edge
  }

  override def toString =
    "\t" + label + ":{\n" +
      (if (!statements.isEmpty) statements.mkString("\t\t", "\n\t\t", "\n") else "") +
      (if (!successors.isEmpty) ("\t\tgoto " + (for (s <- successors) yield {
        s.condition.toString + " ⇒ " + s.target.label + (if(s.isBackEdge) " (backedge)" else "")
      }).mkString(",") + "\n") else "") +
      "\t}\n"

  private val pStatements = new ListBuffer[Statement]
  private val pSuccessors = new ListBuffer[CFGEdge]
  private val pPredecessors = new ListBuffer[CFGEdge]

  private[silAST] def appendStatement(s: Statement) = {
    require(!(pStatements contains s))
    pStatements += s
  }

  def statements: Seq[Statement] = pStatements.result()

  def successors: Set[CFGEdge] = pSuccessors.result().toSet

  def predecessors: Set[CFGEdge] = pPredecessors.result().toSet

  private[silAST] val pLocalVariables = new ListBuffer[ProgramVariable]

  def localVariables : Set[ProgramVariable] = pLocalVariables.toSet

//  cfg.addNode(this)

  var expressionFactory : ExpressionFactory = pFactory

  private[silAST] var pFactory : BasicBlockFactory = null
  
  private[implementations] var cfg : ControlFlowGraph = null
}
