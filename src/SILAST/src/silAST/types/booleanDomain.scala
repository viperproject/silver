package silAST.types

import silAST.domains._
import silAST.expressions.util.TermSequence
import silAST.source.noLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Integer
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
object booleanDomain extends Domain {
  override def name = "Boolean"

  override def fullName: String = name

  override val sourceLocation = noLocation

  override def functions = Set[DomainFunction](booleanTrue, booleanFalse, booleanConjunction, booleanDisjunction, booleanNegation, booleanImplication, booleanEquivalence)

  override def predicates = Set(booleanEvaluate)

  override def axioms = Set.empty[DomainAxiom]

  override def substitute(ts: TypeVariableSubstitution) = this

  override def getType = booleanType

  override def freeTypeVariables = Set()

  override def isCompatible(other: Domain) = other == this
}

object booleanType extends NonReferenceDataType(booleanDomain)(noLocation)

///////////////////////////////////////////////////////////////////////////
object booleanTrue extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "true"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 0)
    name
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanFalse extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "false"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 0)
    name
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanNegation extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "!"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 1)
    name + ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanConjunction extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "/\\"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanDisjunction extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "\\/"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanImplication extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "=>"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanEquivalence extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "<=>"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanEvaluate extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = "eval"
  override val signature = new DomainPredicateSignature(DataTypeSequence(booleanType))(noLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 1)
    ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}
