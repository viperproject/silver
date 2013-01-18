package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.types.{TypeVariable, DataType}
import semper.sil.ast.source.{NoLocation, SourceLocation}
import semper.sil.ast.expressions.Expression

final case class Function private[programs](
                                             name: String,
                                             pParams: Seq[(SourceLocation, String, DataType)],
                                             resultType: DataType
                                             )(
                                             val sourceLocation: SourceLocation,
                                             val factory: FunctionFactory, val comment: List[String])
  extends ASTNode {
  private[symbols] var pSignature = new FunctionSignature(pParams, resultType)(NoLocation, Nil)

  lazy val signature: FunctionSignature = pSignature
  lazy val freeTypeVariables: Set[TypeVariable] = signature.freeTypeVariables

  override def toString = "function " + name + signature.toString + " = " + body.toString

  def body: Expression = pBody.get

  private[symbols] var pBody: Option[Expression] = None

  override def equals(other: Any): Boolean = {
    other match {
      case f: Function => this eq f
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}