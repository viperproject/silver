package silAST.programs

import silAST.symbols.Field
import silAST.symbols.Implementation
import silAST.symbols.Method
import silAST.ASTNode
import silAST.domains.Domain
import silAST.symbols.Predicate
import silAST.symbols.Function
import silAST.source.SourceLocation


abstract class Program private[programs](
    sl : SourceLocation,
    val name: String
  ) extends ASTNode(sl)
{
  val domains: Set[Domain]
  val fields: Set[Field]
  val functions: Set[Function]
  val predicates: Set[Predicate]
  val methods: Set[Method]
}

object Program
{
  def getFactory(name : String) : ProgramFactory = new ProgramFactory(name)
}