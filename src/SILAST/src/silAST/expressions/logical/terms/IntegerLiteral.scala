package silAST.expressions.domain.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.LiteralTerm
import silAST.AtomicNode

class IntegerLiteral( sl : SourceLocation, val value:BigInt) extends LiteralTerm(sl) with AtomicNode{
  override def toString : String = value.toString()
}