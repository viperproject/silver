package silAST.programs

import silAST.source.SourceLocation
import silAST.expressions.terms.{DomainTerm, ProgramTerm, GeneralTerm, Term}
import silAST.expressions._
import collection.mutable.HashSet


private[silAST] trait ExpressionFactory extends NodeFactory {
  //////////////////////////////////////////////////////////////////////////
/*  def makeEqualityExpression(sl: SourceLocation,t1: Term,t2: Term): EqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case (t1: ProgramTerm, t2: ProgramTerm) => makePEqualityExpression(sl,t1,t2)
      case (t1: DomainTerm, t2: DomainTerm)   => makeDEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new EqualityExpression(sl, t1, t2) )
    }
  }
  */
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //Equality
  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(sl: SourceLocation,t1: Term,t2: Term): EqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case (t1: ProgramTerm, t2: ProgramTerm) => makePEqualityExpression(sl,t1,t2)
      case (t1: DomainTerm, t2: DomainTerm)   => makeDEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new EqualityExpression(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(sl: SourceLocation,t1: ProgramTerm,t2: ProgramTerm) : PEqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new PEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDEqualityExpression(sl: SourceLocation,t1: DomainTerm,t2: DomainTerm) : DEqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression[DEqualityExpression]( new DEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGEqualityExpression(
                              sl: SourceLocation,
                              t1: GeneralTerm,
                              t2: GeneralTerm
                              ): GEqualityExpression =
  {
    require(terms.contains(t1))
    require(terms.contains(t2))
    addExpression ( new GEqualityExpression(sl, t1, t2) )
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private def addExpression[E <: Expression](e: E)  : E = {
    expressions + e
    nodeMap += e.sourceLocation -> e    //Overrides sub expressions - always largest in the map
    e
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected val terms = new HashSet[Term]
  protected val expressions = new HashSet[Expression]

}