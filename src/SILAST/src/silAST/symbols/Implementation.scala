package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.statements.ControlFlowGraph

class Implementation private[silAST](
  sl : SourceLocation,
  val method: Method,
  val locals: List[ProgramVariable],
  val body : ControlFlowGraph
) extends ASTNode(sl) {
  override def subNodes = locals ++ (body :: Nil)
}