package silAST.methods.implementations

import silAST.ASTNode
import silAST.methods.Method
import silAST.programs.symbols.ProgramVariable
import collection.mutable.ListBuffer
import silAST.source.{noLocation, SourceLocation}

final class Implementation private[silAST](
                                            sl: SourceLocation,
                                            val method: Method
                                            ) extends ASTNode(sl) {
  override def toString = "implementation " + method.name + method.signature.toString +
    "{" +
    locals.mkString("\n\t", "\t", "\n") +
    body.toString +
    "}"

  private[silAST] val pLocals = new ListBuffer[ProgramVariable]
  private[silAST] val pBody = new ControlFlowGraph(noLocation)

  def locals: Seq[ProgramVariable] = pLocals

  def body: ControlFlowGraph = pBody

  override def subNodes = locals ++ (body :: Nil)
}