package silAST.expressions.program
import silAST.source.SourceLocation
import silAST.expressions.logical.LogicalTermNode

abstract class ProgramTermNode[+T <: ProgramTermNode[T]](sl : SourceLocation) extends LogicalTermNode(sl) {

}