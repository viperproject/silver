package silAST.expressions.logical.terms
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class GLogicalTerm[+T <:GLogicalTerm[T]](sl : SourceLocation) extends ASTNode(sl) {
  type LogicalTerm = GLogicalTerm[LogicalTermTrait];
  def subTerms(): Seq[GLogicalTerm[T]]
}