package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm
import silAST.expressions.GExpression

trait GProgramExpression[+T <: GTerm[T]] extends GExpression[T] 
{
}