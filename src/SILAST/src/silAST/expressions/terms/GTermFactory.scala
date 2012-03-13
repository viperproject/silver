package silAST.expressions.terms

import silAST.source.SourceLocation
import collection.mutable.HashSet
import collection.Set
import silAST.domains.DomainFunction
import silAST.expressions.util.GTermSequence
import silAST.programs.NodeFactory
import silAST.types.booleanType

protected[silAST] trait GTermFactory 
  extends NodeFactory 
{
/*  /////////////////////////////////////////////////////////////////////////
  def migrateG(t : Term)
  {
    t match {
      case gt : GTerm => migrateG(gt)
      case _ => throw new Exception("Tried to migrateG invalid expression " + t.toString)
    }
  }
  */
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateG(t : GTerm)
  {
    if (terms contains t)
      return;
    t match
    {
      case t : LiteralTerm => addTerm(t)
      case fa : GDomainFunctionApplicationTerm => {
        require(domainFunctions contains  fa.function)
        fa.arguments.foreach(migrateG(_))
        addTerm(fa)
      }
      case itet : GIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrateG(itet.condition)
        migrateG(itet.pTerm)
        migrateG(itet.nTerm)
      }
    }
  }
  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralTerm(sourceLocation : SourceLocation, v: BigInt): IntegerLiteralTerm = {
    addTerm(new IntegerLiteralTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: GTermSequence): GDomainFunctionApplicationTerm = {
    a.foreach(migrateG (_))
    require(domainFunctions contains f)
    addTerm(new GDomainFunctionApplicationTerm(f, a)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGIfThenElseTerm(sourceLocation : SourceLocation, c : GTerm,  p:GTerm,  n : GTerm): GIfThenElseTerm = {
    migrateG(c)
    migrateG(p)
    migrateG(n)
    require(c.dataType == booleanType)
    addTerm(new GIfThenElseTerm(c,p,n)(sourceLocation))
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