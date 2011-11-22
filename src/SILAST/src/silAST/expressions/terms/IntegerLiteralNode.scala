package silAST.expressions.terms
import silAST.source.SourceLocation

class IntegerLiteral( sl : SourceLocation, val value:BigInt) extends LiteralNode(sl) {

  override def toString(): String = { return value.toString(); }

}