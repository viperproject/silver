package silAST.expressions.logical.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class LogicalTermNode[+T <: LogicalTermNode[T]](sl : SourceLocation) extends TermNode[T](sl) {

}