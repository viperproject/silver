package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.logical.GLogicalExpression
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.source.SourceLocation
import silAST.expressions.program.GProgramExpression

trait GDomainExpression[+T <: GLogicalTerm[T]] extends GLogicalExpression[T] {

  def subExpressions(): Seq[GLogicalExpression[T]]

}