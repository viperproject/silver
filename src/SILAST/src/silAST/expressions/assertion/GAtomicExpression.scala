package silAST.expressions.assertion

import scala.collection.Seq
import silAST.expressions.assertion.terms.GTerm

trait GAtomicExpression[+T <: GTerm[T]] extends AtomicExpression {

  def subTerms(): Seq[GTerm[T]] = { null }

}