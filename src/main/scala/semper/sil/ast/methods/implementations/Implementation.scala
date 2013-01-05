package semper.sil.ast.methods.implementations

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.methods.{Scope, Method}

final class Implementation private[sil]
(
  val method: Method,
  override val factory: ImplementationFactory
  )(override val sourceLocation: SourceLocation, val comment: List[String])
  extends Scope {
  val parentScope: Option[Scope] = Some(method)

  def body: ControlFlowGraph = pBody

  val implementation = this

  //////////////////////////////////////////////////////////////////
  override def equals(other: Any): Boolean = {
    other match {
      case i: Implementation => this eq i
      case _ => false
    }
  }

  override def hashCode(): Int = method.name.hashCode()

  override def toString = "implementation " + method.name + method.signature.toString +
    "{" +
    (for (l <- locals) yield "var " + l.name + " : " + l.dataType).mkString("\n\t", "\n\t", "\n") +
    body.toString +
    "}"

  //////////////////////////////////////////////////////////////////
  protected[sil] var pBody: ControlFlowGraph = null
}