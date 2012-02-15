package silAST.programs

import scala.collection.Set
import silAST.ASTNode
import silAST.domains.Domain
import silAST.source.SourceLocation
import symbols.{Field, Predicate, Function}
import silAST.methods.Method


final class Program private[silAST](
                                     val sourceLocation : SourceLocation,
                                     val name: String,
                                     val domains: Set[Domain],
                                     val fields: Set[Field],
                                     val functions: Set[Function],
                                     val predicates: Set[Predicate],
                                     val methods: Set[Method],
                                     val factory : ProgramFactory
                                     ) extends ASTNode {
  override def toString =
    "program " + name + "\n" +
      domains.mkString("", "\n", "\n") +
      fields.mkString("", "\n", "\n") +
      functions.mkString("", "\n", "\n") +
      predicates.mkString("", "\n", "\n") +
      methods.mkString("\n", "\n", "\n\n")

  override def equals(other : Any) : Boolean =
  {
    other match{
      case p : Program => this eq p
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}

object Program {

  def getFactory(sourceLocation : SourceLocation, name: String): ProgramFactory = new ProgramFactory(sourceLocation, name)
}
