package silAST.methods.implementations

import silAST.source.SourceLocation
import silAST.methods.{Scope, Method}

final class Implementation private[silAST]
  (
    override val sourceLocation: SourceLocation,
    val method: Method,
    override val factory: ImplementationFactory
  )
  extends Scope
{
  val parentScope: Option[Scope] = Some(method)

  def body: ControlFlowGraph = pBody

  val implementation = this

  System.out.println(
    "Implementation " + method.name + " pvs" +programVariables.mkString(",") +
      " method.pvs: " + method.programVariables.mkString(",") +
      " method.params: " + method.signature.parameters.mkString(",") +
      " method.results: " + method.signature.results.mkString(",")
  )
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
  protected[silAST] var pBody : ControlFlowGraph = null
}