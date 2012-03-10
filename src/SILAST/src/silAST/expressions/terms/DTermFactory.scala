package silAST.expressions.terms

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.LogicalVariable
import collection.mutable.HashSet
import silAST.domains.DomainFunction
import silAST.types.{DataTypeFactory, DataType}
import silAST.expressions.util.{DTermSequence, GTermSequence}


trait DTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {

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
  protected[silAST] val boundVariables = new HashSet[LogicalVariable]
}