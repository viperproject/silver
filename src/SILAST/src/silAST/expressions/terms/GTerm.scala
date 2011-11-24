package silAST.expressions.terms
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class GTerm[+T <:GTerm[T]](sl : SourceLocation) extends Term(sl)
{
  def subTerms(): Seq[GTerm[T]]
}