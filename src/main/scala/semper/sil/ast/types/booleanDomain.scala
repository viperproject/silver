package semper.sil.ast.types

import semper.sil.ast.domains._
import semper.sil.ast.expressions.util.ExpressionSequence
import semper.sil.ast.source.NoLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Integer
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
object booleanDomain extends Domain {
  override def name = "Boolean"

  override def comment = List()

  override def fullName: String = name

  override val sourceLocation = NoLocation

  override def functions = Set[DomainFunction](booleanTrue, booleanFalse, booleanConjunction, booleanDisjunction, booleanNegation, booleanImplication, booleanEquivalence)

  override def predicates = Set(booleanEvaluate)

  override def axioms = Set.empty[DomainAxiom]

  override def substitute(ts: TypeVariableSubstitution) = this

  override def getType = booleanType

  override def freeTypeVariables = Set()

  override def isCompatible(other: Domain) = other == this
}

object booleanType extends NonReferenceDataType(booleanDomain)(NoLocation, Nil)

///////////////////////////////////////////////////////////////////////////
object booleanTrue extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "true"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 0)
    name
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanFalse extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "false"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 0)
    name
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanNegation extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "!"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 1)
    name + ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanConjunction extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "/\\"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanDisjunction extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "\\/"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanImplication extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "=>"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanEquivalence extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "<=>"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(booleanType, booleanType), booleanType)(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + name + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object booleanEvaluate extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = "eval"
  override val signature = new DomainPredicateSignature(DataTypeSequence(booleanType))(NoLocation)
  override lazy val domain = booleanDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 1)
    ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}
