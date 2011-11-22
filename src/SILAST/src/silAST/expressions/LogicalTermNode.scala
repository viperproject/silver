package silAST.expressions
import silAST.source.SourceLocation

abstract class LogicalTermNode[+T <: LogicalTermNode[T]](sl : SourceLocation) extends TermNode[T](sl) {

}