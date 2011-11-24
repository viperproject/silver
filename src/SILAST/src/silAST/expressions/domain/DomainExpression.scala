package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.domain.terms.DomainTerm
import silAST.source.SourceLocation

abstract trait DomainExpression extends GDomainExpression[DomainTerm] {
}