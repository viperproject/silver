package silAST.expressions
import silAST.expressions.terms.Term

trait AtomicExpression extends Expression {
  override def subExpressions = Nil
  
  def subTerms : Seq[Term]
}