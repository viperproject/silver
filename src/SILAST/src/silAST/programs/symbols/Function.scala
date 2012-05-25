package silAST.programs.symbols

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.types.DataType
import silAST.source.{noLocation, SourceLocation}

final case class Function private[programs](
                                        name: String,
                                        pParams: Seq[(SourceLocation, String, DataType)],
                                        resultType: DataType
                                        )(
                                          val sourceLocation: SourceLocation,
                                          val factory: FunctionFactory)
                                        extends ASTNode {
  private[symbols] var pSignature = new FunctionSignature(pParams, resultType)(noLocation)

  lazy val signature: FunctionSignature = pSignature

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