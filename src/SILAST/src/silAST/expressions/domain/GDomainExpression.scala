package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.logical.GLogicalExpression
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.source.SourceLocation
import silAST.expressions.program.GProgramExpression

abstract class GDomainExpression[+T <: GLogicalTerm[T]](sl : SourceLocation) extends GLogicalExpression[T](sl) {

  def subExpressions(): Seq[GLogicalExpression[T]]

}