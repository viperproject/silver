package silAST.expressions.terms

import silAST.source.SourceLocation
import collection.mutable.{HashMap, HashSet}
import collection.immutable.{Map}
import silAST.domains.DomainFunction
import silAST.expressions.util.{GTermSequence, TermSequence}
import silAST.programs.NodeFactory

protected[silAST] trait GTermFactory extends NodeFactory
{
  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralTerm(sl : SourceLocation, v : BigInt) : IntegerLiteralTerm = {
    addTerm( new IntegerLiteralTerm(sl,v))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGDomainFunctionApplicationTerm(sl : SourceLocation, f : DomainFunction, a : GTermSequence) : GDomainFunctionApplicationTerm =
  {
    require(termSequences.contains(a))
    require(domainFunctions(f.name) == f)
    addTerm(new GDomainFunctionApplicationTerm(sl,f,a))
  }


  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def makeGTermSequence(sl : SourceLocation, ts : Seq[GTerm]) : GTermSequence = {
    require( ts.toSet subsetOf terms)
    val result = new GTermSequence(sl,ts)
    termSequences += result
    result
  }
  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def addTerm[T <: Term](t: T): T = {
    terms += t
    t
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] val terms = new HashSet[Term]
  protected[silAST] val termSequences = new HashSet[TermSequence]
  protected[silAST] def domainFunctions  : Map[String, DomainFunction] // = new HashMap[String, DomainFunction]
}