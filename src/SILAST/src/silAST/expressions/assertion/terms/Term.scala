package silAST.expressions.assertion.terms
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class Term(sl : SourceLocation) extends ASTNode(sl) {
  def subTerms(): Seq[Term]
}
