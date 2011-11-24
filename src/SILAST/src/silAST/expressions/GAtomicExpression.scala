package silAST.expressions

import scala.collection.Seq
import silAST.expressions.terms.GTerm

trait GAtomicExpression[+T <: GTerm[T]] extends AtomicExpression {

  def subTerms(): Seq[GTerm[T]] = Nil

}