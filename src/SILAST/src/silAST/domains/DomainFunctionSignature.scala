package silAST.domains

import silAST.ASTNode
import silAST.types.DataType
import silAST.symbols.DataTypeSequence

abstract class DomainFunctionSignature extends ASTNode 
{
	val argumentTypes : DataTypeSequence
	val resultType    : DataType
}