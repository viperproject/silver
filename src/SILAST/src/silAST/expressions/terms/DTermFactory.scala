package silAST.expressions.terms

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.LogicalVariable
import collection.mutable.HashSet
import silAST.domains.DomainFunction
import silAST.expressions.util.{DTermSequence, GTermSequence}
import silAST.types.{booleanType, DataTypeFactory, DataType}


trait DTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
/*
  /////////////////////////////////////////////////////////////////////////
  override def migrate(t : Term)
  {
    t match {
      case dt : DTerm => migrate(dt)
      case _ => throw new Exception("Tried to migrate invalid expression " + t.toString)
    }
  }
  */
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateD(t : DTerm)
  {
    if (terms contains t)
      return;
    t match
    {
      case gt : GTerm => migrateG(gt)
      case lv : LogicalVariableTerm => 
      {
        require(boundVariables contains lv.variable)
        addTerm(lv)
      }
      case fa : DDomainFunctionApplicationTerm =>
      {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrateD(_))
        addTerm(fa)
      }
      case itet : DIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrateD(itet.condition)
        migrateD(itet.pTerm)
        migrateD(itet.nTerm)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def validBoundVariableName(name:String) : Boolean =
    name!="this"

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariable(sourceLocation : SourceLocation, name: String, dataType: DataType): LogicalVariable = {
    require(dataTypes contains dataType)
    require(validBoundVariableName(name))
    val result: LogicalVariable = new LogicalVariable(name, dataType)(sourceLocation)
    boundVariables += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariableTerm(sourceLocation : SourceLocation, v: LogicalVariable): LogicalVariableTerm = {
    require(boundVariables contains v)
    addTerm(new LogicalVariableTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: DTermSequence): DDomainFunctionApplicationTerm = {
    require(a != null)
    require(a.forall(_ != null))
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new DDomainFunctionApplicationTermC(f, a)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDIfThenElseTerm(sourceLocation : SourceLocation, c : DTerm,  p:DTerm,  n : DTerm): DIfThenElseTerm = {
    migrateD(c)
    migrateD(p)
    migrateD(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc:GTerm, gp:GTerm,gn:GTerm) => makeGIfThenElseTerm(sourceLocation,gc,gp,gn)
      case _ => addTerm(new DIfThenElseTermC(c,p,n)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] val boundVariables = new HashSet[LogicalVariable]
}