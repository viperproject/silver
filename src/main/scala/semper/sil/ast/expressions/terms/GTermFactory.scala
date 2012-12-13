package semper.sil.ast.expressions.terms

import semper.sil.ast.source.SourceLocation
import collection.mutable.HashSet
import collection.{mutable, Set}
import semper.sil.ast.domains.DomainFunction
import semper.sil.ast.expressions.util.GTermSequence
import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.types.booleanType

protected[sil] trait GTermFactory
  extends NodeFactory {
  /////////////////////////////////////////////////////////////////////////
  protected[sil] def migrate(t: GTerm) {
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
  protected[sil] def addTerm[T <: Term](t: T): T = {
    terms += t
    t
  }

  /////////////////////////////////////////////////////////////////////////
  protected val terms = new mutable.HashSet[Term]

  protected[sil] def domainFunctions: Set[DomainFunction]
}