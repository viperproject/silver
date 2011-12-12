package silAST.programs.symbols

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.types.DataType
import silAST.source.{noLocation, SourceLocation}

final class Function private[programs](
                                        sl: SourceLocation,
                                        val name: String,
                                        pParams  : Seq[(SourceLocation, String, DataType)],
                                        resultType : DataType
                                        ) extends ASTNode(sl)
{
  private[symbols] var pSignature = new FunctionSignature(noLocation, pParams, resultType)

  def signature: FunctionSignature = if (pBody == None) throw new Exception else pSignature

  override def toString = "function " + name + signature.toString + " = " + body.toString

  def body: Term = pBody.get

  private[symbols] var pBody: Option[Term] = None
}