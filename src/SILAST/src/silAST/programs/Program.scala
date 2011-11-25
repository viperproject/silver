package silAST.programs

import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.symbols.Implementation
import silAST.symbols.Method
import silAST.ASTNode
import silAST.domains.Domain
import silAST.symbols.Predicate
import silAST.symbols.Function


abstract class Program extends ASTNode 
{
	val name : String
	val domains : Set[Domain]
	val fields : Set[Field]
	val functions : Set[Function]
	val predicates : Set[Predicate]
	val methods : Set[Method]
	val implementations : Set[Implementation]
}