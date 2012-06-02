package silAST.expressions.terms

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.LogicalVariable
import collection.mutable.HashSet
import silAST.expressions.util.{DTermSequence, GTermSequence}
import silAST.types.{booleanType, DataTypeFactory, DataType}
import collection.immutable
import silAST.programs.symbols.ProgramVariable
import silAST.domains._
import silAST.expressions.{DProgramVariableSubstitutionC, DProgramVariableSubstitution}


trait DTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeDProgramVariableSubstitution(subs: immutable.Set[(ProgramVariable, DTerm)]): DProgramVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new DProgramVariableSubstitutionC(subs, Set())
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDLogicalVariableSubstitution(subs: immutable.Set[(LogicalVariable, DTerm)]): DLogicalVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new DLogicalVariableSubstitutionC(Set(), subs)
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t: DTerm) {
    if (terms contains t)
      return;
    t match {
      case gt: GTerm => super.migrate(gt)
      case lv: LogicalVariableTerm => {
        require(boundVariables contains lv.variable)
        addTerm(lv)
      }
      case fa: DDomainFunctionApplicationTerm => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case itet: DIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def validBoundVariableName(name: String): Boolean =
    name != "this"

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariable(name: String, dataType: DataType,sourceLocation: SourceLocation,comment : List[String] = Nil): LogicalVariable = {
    require(dataTypes contains dataType)
    require(validBoundVariableName(name))
    val result: LogicalVariable = new LogicalVariable(name, dataType)(sourceLocation,comment)
    boundVariables += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariableTerm(v: LogicalVariable,sourceLocation: SourceLocation,comment : List[String] = Nil): LogicalVariableTerm = {
    require(boundVariables contains v)
    addTerm(new LogicalVariableTerm(v)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDDomainFunctionApplicationTerm(f: DomainFunction, a: DTermSequence,sourceLocation: SourceLocation,comment : List[String] = Nil): DDomainFunctionApplicationTerm = {
    require(a != null)
    require(a.forall(_ != null))
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(f, a,sourceLocation,comment)
      case _ => addTerm(new DDomainFunctionApplicationTermC(f, a)(sourceLocation,comment))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDIfThenElseTerm(c: DTerm, p: DTerm, n: DTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): DIfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc: GTerm, gp: GTerm, gn: GTerm) => makeGIfThenElseTerm(gc, gp, gn,sourceLocation,comment)
      case _ => addTerm(new DIfThenElseTermC(c, p, n)(sourceLocation,comment))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] val boundVariables = new HashSet[LogicalVariable]
}