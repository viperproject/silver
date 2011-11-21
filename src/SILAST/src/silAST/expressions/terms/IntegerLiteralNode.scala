package silAST.expressions.terms
import source.SourceLocation

class IntegerLiteral(val value:BigInt,val sl : SourceLocation) extends Literal(sl) {

  override def toString(): String = { return value.toString(); }

}