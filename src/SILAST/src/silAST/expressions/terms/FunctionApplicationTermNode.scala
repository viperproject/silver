package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.expressions.ProgramTermNode
import silAST.symbols.ArgumentSequence
import silAST.symbols.Function
import silAST.source.SourceLocation
import silAST.expressions.TermNode

class FunctionApplicationTermNode[+T <: TermNode[T]](sl:SourceLocation,val function : Function, val arguments : ArgumentSequence[T] ) 
	extends TermNode[T](sl) 
{

  override def toString(): String = { 
    return function.name + arguments.toString();
  }

  override def subNodes(): Seq[T] = { return arguments.asSeq }

}