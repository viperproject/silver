package silAST.expressions.assertion
import silAST.expressions.assertion.terms.Term

trait AtomicExpression extends Expression {
  override def subExpressions = Nil
  
  def subTerms : Seq[Term]
}