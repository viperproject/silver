package semper.sil.ast.programs

import scala.collection.Set
import semper.sil.ast.ASTNode
import semper.sil.ast.domains.Domain
import semper.sil.ast.source.SourceLocation
import symbols.{Field, Predicate, Function}
import semper.sil.ast.methods.{Scope, Method}


final class Program private[sil]
(

  val name: String,
  val domains: Set[Domain],
  val fields: Set[Field],
  val functions: Set[Function],
  val predicates: Set[Predicate],
  val methods: Set[Method],
  val factory: ProgramFactory
  )(val sourceLocation: SourceLocation, val comment: List[String]) extends ASTNode with Scope {
  override val parentScope = None

  override def toString =
    "program " + name + "\n" +
      domains.mkString("", "\n", "\n") +
      fields.mkString("", "\n", "\n") +
      functions.mkString("", "\n", "\n") +
      predicates.mkString("", "\n", "\n") +
      methods.mkString("\n", "\n", "\n\n")

  override def equals(other: Any): Boolean = {
    other match {
      case p: Program => this eq p
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}

object Program {

  def getFactory(name: String, sourceLocation: SourceLocation, comment: List[String] = Nil):
  ProgramFactory = new ProgramFactory(name)(sourceLocation, comment)
}
