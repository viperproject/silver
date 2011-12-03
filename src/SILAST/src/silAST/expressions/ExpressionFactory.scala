package silAST.expressions


/*
private[silAST] trait ProgramExpressionFactory
{
val programFactory : ProgramFactory

def makeEqualityExpression(
sl : SourceLocation,
t1 : ProgramTerm,
t2 : ProgramTerm
) : PEqualityExpression  = {
require (terms.contains(t1))
require (terms.contains(t2))

val result = programFactory.makePEqualityExpression(sl,t1,t2)
expressions.getOrElseUpdate(result.toString,result)

result
}

val terms = new HashSet[ProgramTerm]
val expressions = new HashSet[ProgramExpression]
}
*/