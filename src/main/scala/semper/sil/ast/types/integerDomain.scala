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
object integerDomain extends Domain {
  override val name = "Integer"
  override val comment = Nil

  override def fullName: String = name

  override val sourceLocation = NoLocation

  override def functions = Set[DomainFunction](integerAddition, integerSubtraction, integerMultiplication, integerDivision, integerModulo, integerNegation, integerEQ, integerNE, integerLE, integerLT, integerGE, integerGT)

  override def predicates = Set[DomainPredicate]()

  override def axioms = Set.empty[DomainAxiom]

  override def substitute(ts: TypeVariableSubstitution) = this

  override def getType = integerType

  override def freeTypeVariables = Set()

  override def isCompatible(other: Domain) = other == this
}

object integerType extends NonReferenceDataType(integerDomain)(NoLocation, Nil)

///////////////////////////////////////////////////////////////////////////
object integerAddition extends DomainFunction {
  override lazy val sourceLocation = NoLocation
  override val comment = Nil
  override lazy val name = "+"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts != null)
    require(ts.length == 2)
    ts(0).toString + "+" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerSubtraction extends DomainFunction {
  override lazy val sourceLocation = NoLocation
  override val comment = Nil
  override lazy val name = "-"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "-" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerMultiplication extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "*"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "*" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerDivision extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "/"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "/" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerModulo extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "%"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "%" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerNegation extends DomainFunction {
  override val comment = Nil
  override lazy val sourceLocation = NoLocation
  override lazy val name = "-"
  override lazy val signature = new DomainFunctionSignature(DataTypeSequence(integerType), integerType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 1)
    "-" + ts(0).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerLE extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = "<="
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerLT extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = "<"
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerGE extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = ">="
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerGT extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = ">"
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerEQ extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = "=="
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "==" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerNE extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = NoLocation
  override val name = "!="
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, integerType), booleanType)(NoLocation)
  override lazy val domain = integerDomain

  override def toString(ts: ExpressionSequence) = {
    require(ts.length == 2)
    ts(0).toString + "!=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}
