package silAST.programs

import scala.collection.Set
import silAST.ASTNode
import silAST.domains.Domain
import silAST.source.SourceLocation
import symbols.{Field, Predicate, Function}
import silAST.methods.Method


final class Program private[silAST](
                                     sl: SourceLocation,
                                     val name: String,
                                     val domains: Set[Domain],
                                     val fields: Set[Field],
                                     val functions: Set[Function],
                                     val predicates: Set[Predicate],
                                     val methods: Set[Method]
                                     ) extends ASTNode(sl) {
  override def toString =
    "program " + name + "\n" +
      domains.mkString("", "\n", "\n") +
      fields.mkString("", "\n", "\n") +
      functions.mkString("", "\n", "\n") +
      predicates.mkString("", "\n", "\n") +
      methods.mkString("\n", "\n", "\n\n")
}

object Program {

  def getFactory(sl: SourceLocation, name: String): ProgramFactory = new ProgramFactory(sl, name)
}
