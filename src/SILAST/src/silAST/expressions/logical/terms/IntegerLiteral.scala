package silAST.expressions.domain.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.LiteralTerm
import silAST.expressions.logical.terms.AtomicTerm
import silAST.AtomicNode

class IntegerLiteral( sl : SourceLocation, val value:BigInt) extends LiteralTerm(sl) with AtomicTerm[IntegerLiteral] with AtomicNode{

  override def toString(): String = { return value.toString(); }

}