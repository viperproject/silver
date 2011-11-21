package silAST.expressions.terms
import source.SourceLocation

class BooleanLiteral(val value:Boolean,val sl : SourceLocation) extends Literal(sl) {

  override def toString(): String = { return value.toString(); }

}