package silAST

class IntegerLiteral(val value:BigInt,val sl : SourceLocation) extends Literal(sl) {

  override def toString(): String = { return value.toString(); }

}