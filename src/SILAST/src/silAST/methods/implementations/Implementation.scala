package silAST.methods.implementations

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.methods.Method
import silAST.programs.symbols.ProgramVariable

final class Implementation private[silAST](
                                            sl: SourceLocation,
                                            val method: Method,
                                            val locals: List[ProgramVariable],
                                            val body: ControlFlowGraph
                                            ) extends ASTNode(sl) {
  override def toString = "implementation" + method.name + method.signature.toString + "{" + locals.toString + body.toString + "}"

  override def subNodes = locals ++ (body :: Nil)
}