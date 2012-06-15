package silAST.expressions.terms

import silAST.source.SourceLocation
import collection.mutable.HashSet
import collection.{mutable, Set}
import silAST.domains.DomainFunction
import silAST.expressions.util.GTermSequence
import silAST.programs.NodeFactory
import silAST.types.booleanType

protected[silAST] trait GTermFactory
  extends NodeFactory {
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t: GTerm) {
    if (terms contains t)
      return
    t match {
      case t: LiteralTerm => addTerm(t)
      case fa: GDomainFunctionApplicationTerm => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case itet: GIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralTerm(v: BigInt,sourceLocation: SourceLocation,comment : List[String] =  Nil): IntegerLiteralTerm = {
    addTerm(new IntegerLiteralTerm(v)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGDomainFunctionApplicationTerm(f: DomainFunction, a: GTermSequence,sourceLocation: SourceLocation,comment : List[String] = Nil): GDomainFunctionApplicationTerm = {
    a.foreach(migrate(_))
    require(domainFunctions contains f)
    addTerm(new GDomainFunctionApplicationTerm(f, a)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeGIfThenElseTerm(c: GTerm, p: GTerm, n: GTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): GIfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    addTerm(new GIfThenElseTerm(c, p, n)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def addTerm[T <: Term](t: T): T = {
    terms += t
    t
  }

  /////////////////////////////////////////////////////////////////////////
  protected val terms = new mutable.HashSet[Term]

  protected[silAST] def domainFunctions: Set[DomainFunction]
}