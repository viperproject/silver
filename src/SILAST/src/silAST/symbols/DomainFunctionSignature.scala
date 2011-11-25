package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.types.DataType

abstract class DomainFunctionSignature(
		sl : SourceLocation,
		val argumentTypes : DataTypeSequence,
		val resultType    : DataType
    ) 
	extends ASTNode(sl) 
{
}