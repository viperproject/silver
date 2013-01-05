package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.terms.Term
import semper.sil.ast.types.{TypeVariable, DataType}
import semper.sil.ast.source.{noLocation, SourceLocation}

final case class Function private[programs](
                                             name: String,
                                             pParams: Seq[(SourceLocation, String, DataType)],
                                             resultType: DataType
                                             )(
                                             val sourceLocation: SourceLocation,
                                             val factory: FunctionFactory, val comment: List[String])
  extends ASTNode {
  private[symbols] var pSignature = new FunctionSignature(pParams, resultType)(noLocation, Nil)

  lazy val signature: FunctionSignature = pSignature
  lazy val freeTypeVariables: Set[TypeVariable] = signature.freeTypeVariables

  override def toString = "function " + name + signature.toString + " = " + body.toString

  def body: Term = pBody.get

  private[symbols] var pBody: Option[Term] = None

  override def equals(other: Any): Boolean = {
    other match {
      case f: Function => this eq f
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}