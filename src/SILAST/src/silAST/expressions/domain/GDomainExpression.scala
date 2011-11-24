package silAST.expressions.domain

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.program.GProgramExpression
import silAST.expressions.terms.GTerm
import silAST.expressions.GExpression

trait GDomainExpression[+T <: GTerm[T]] extends GExpression[T] {

  def subExpressions(): Seq[GExpression[T]]

}