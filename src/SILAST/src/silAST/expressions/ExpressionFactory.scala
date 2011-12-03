package silAST.expressions


/*
private[silAST] trait ProgramExpressionFactory
{
val programFactory : ProgramFactory

def makeEqualityExpression(
sl : SourceLocation,
t1 : PTerm,
t2 : PTerm
) : PEqualityExpression  = {
require (terms.contains(t1))
require (terms.contains(t2))

val result = programFactory.makePEqualityExpression(sl,t1,t2)
expressions.getOrElseUpdate(result.toString,result)

result
}

val terms = new HashSet[PTerm]
val expressions = new HashSet[PExpression]
}
*/