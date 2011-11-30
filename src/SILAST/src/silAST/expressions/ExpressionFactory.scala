package silAST.expressions

import silAST.programs.ProgramFactory
import silAST.source.SourceLocation
import terms.{ProgramTerm}
import collection.mutable.{HashSet,HashMap}
              /*
private[silAST] trait ProgramExpressionFactory
{
  val programFactory : ProgramFactory

  def makeEqualityExpression(
    sl : SourceLocation,
    term1 : ProgramTerm,
    term2 : ProgramTerm
  ) : PEqualityExpression  = {
    require (terms.contains(term1))
    require (terms.contains(term2))

    val result = programFactory.makePEqualityExpression(sl,term1,term2)
    expressions.getOrElseUpdate(result.toString,result)

    result
  }

  val terms = new HashSet[ProgramTerm]
  val expressions = new HashSet[ProgramExpression]
}
              */