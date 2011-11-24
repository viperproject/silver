package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.logical.GLogicalExpression
import silAST.source.SourceLocation
import silAST.expressions.program.GProgramExpression
import silAST.expressions.assertion.terms.GTerm

trait GDomainExpression[+T <: GTerm[T]] extends GLogicalExpression[T] {

  def subExpressions(): Seq[GLogicalExpression[T]]

}