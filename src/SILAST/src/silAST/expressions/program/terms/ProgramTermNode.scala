package silAST.expressions.program.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.LogicalTermNode
import silAST.expressions.terms.TermNode

abstract class ProgramTermNode[+T <: TermNode[T]](sl : SourceLocation) extends LogicalTermNode(sl) {

}