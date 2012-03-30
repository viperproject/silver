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
object integerDomain extends Domain {
  override def name = "Integer"

  override def fullName: String = name

  override val sourceLocation = noLocation

  override def functions = Set[DomainFunction](integerAddition, integerSubtraction, integerMultiplication, integerDivision, integerModulo, integerNegation)

  override def predicates = Set(integerEQ, integerNE, integerLE, integerLT, integerGE, integerGT)

  override def axioms = Set.empty[DomainAxiom]

  override def substitute(ts: TypeVariableSubstitution) = this

  override def getType = integerType

  override def freeTypeVariables = Set()

  override def isCompatible(other: Domain) = other == this
}

object integerType extends NonReferenceDataType(integerDomain)(noLocation)

///////////////////////////////////////////////////////////////////////////
object integerAddition extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "+"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + "+" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerSubtraction extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "-"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "-" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerMultiplication extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "*"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "*" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerDivision extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "/"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "/" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerModulo extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "%"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "%" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerNegation extends DomainFunction {
  override lazy val sourceLocation = noLocation
  override lazy val name = "-"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType), integerType)(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 1)
    "-" + ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerLE extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = "<="
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerLT extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = "<"
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerGE extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = ">="
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerGT extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = ">"
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerEQ extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = "=="
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "==" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerNE extends DomainPredicate {
  override val sourceLocation = noLocation
  override val name = "!="
  override val signature = new DomainPredicateSignature(DataTypeSequence(integerType, integerType))(noLocation)
  override lazy val domain = integerDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "!=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this
}
