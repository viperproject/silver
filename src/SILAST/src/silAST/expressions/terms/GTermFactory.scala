package silAST.expressions.terms

import silAST.source.SourceLocation
import collection.mutable.HashSet
import collection.Set
import silAST.domains.DomainFunction
import silAST.expressions.util.GTermSequence
import silAST.programs.NodeFactory

protected[silAST] trait GTermFactory 
  extends NodeFactory 
{
/*  /////////////////////////////////////////////////////////////////////////
  def migrate(t : Term)
  {
    t match {
      case gt : GTerm => migrate(gt)
      case _ => throw new Exception("Tried to migrate invalid expression " + t.toString)
    }
  }
  */
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t : GTerm)
  {
    if (terms contains t)
      return;
    t match
    {
      case t : LiteralTerm => addTerm(t)
      case fa : GDomainFunctionApplicationTerm => {
        require(domainFunctions contains  fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
    }
  }
  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralTerm(sourceLocation : SourceLocation, v: BigInt): IntegerLiteralTerm = {
    addTerm(new IntegerLiteralTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: GTermSequence): GDomainFunctionApplicationTerm = {
    a.foreach(migrate (_))
    require(domainFunctions contains f)
    addTerm(new GDomainFunctionApplicationTerm(f, a)(sourceLocation))
  }


  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def addTerm[T <: Term](t: T): T = {
    terms += t
    t
  }

  /////////////////////////////////////////////////////////////////////////
  protected val terms = new HashSet[Term]

  protected[silAST] def domainFunctions: Set[DomainFunction]
}