package silAST.expressions.terms
import silAST.source.SourceLocation

class BooleanLiteralNode(sl : SourceLocation, val value:Boolean) extends LiteralNode(sl) {

  override def toString(): String = { return value.toString(); }
}