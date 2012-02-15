package silAST.methods.implementations

import silAST.ASTNode
import silAST.methods.Method
import silAST.programs.symbols.ProgramVariable
import collection.mutable.ListBuffer
import silAST.source.{noLocation, SourceLocation}
import silAST.expressions.ExpressionFactory

final class Implementation private[silAST](
                                            val sourceLocation: SourceLocation,
                                            val method: Method,
                                            private[silAST] val factory : ImplementationFactory
                                            ) extends ASTNode {
  override def toString = "implementation " + method.name + method.signature.toString +
    "{" +
    (for (l <- locals) yield "var " + l.name + " : " + l.dataType).mkString("\n\t", "\n\t", "\n") +
    body.toString +
    "}"

  private[silAST] val pLocals = new ListBuffer[ProgramVariable]

  private[silAST] val pBody = new ControlFlowGraph(noLocation,factory)

  def locals: Seq[ProgramVariable] = pLocals

  def body: ControlFlowGraph = pBody

  lazy val expressionFactory : ExpressionFactory = factory

  override def equals(other : Any) : Boolean = {
    other match{
      case i : Implementation => this eq  i
      case _ => false
    }
  }
  override def hashCode() : Int = method.name.hashCode()
}