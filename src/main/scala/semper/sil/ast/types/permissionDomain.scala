package semper.sil.ast.types

import semper.sil.ast.expressions.util.TermSequence
import semper.sil.ast.source.noLocation
import semper.sil.ast.domains._

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Permissions
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

object permissionDomain extends Domain {
  override val name = "Permission"
  override val comment = Nil
  override val sourceLocation = noLocation

  override def fullName: String = name

  override def functions = Set(permissionAddition, permissionSubtraction, permissionMultiplication, permissionIntegerMultiplication, percentagePermission)

  override def predicates = Set(permissionEQ, permissionNE, permissionLT, permissionLE, permissionGT, permissionGE)

  override val freeTypeVariables = Set[TypeVariable]()

  override def getType = permissionType

  override val axioms = Set[DomainAxiom]()

  override def isCompatible(other: Domain) = other == permissionDomain

  override def substitute(s: TypeVariableSubstitution) = this
}

object permissionType extends NonReferenceDataType(permissionDomain)(noLocation, Nil)


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object permissionAddition extends DomainFunction {
  override val domain = permissionDomain
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "+"
  override val signature = new DomainFunctionSignature(DataTypeSequence(permissionType, permissionType), permissionType)(noLocation)


  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "+" + ts(1).toString
  }

}

object percentagePermission extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "%"
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType), permissionType)(noLocation)
  override val domain = permissionDomain

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this

  override def toString(ts: TermSequence) = {
    require(ts.length == 1)
    ts.head.toString + "%"
  }
}

object permissionSubtraction extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "-"
  override val signature = new DomainFunctionSignature(DataTypeSequence(permissionType, permissionType), permissionType)(noLocation)
  override val domain = permissionDomain

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "-" + ts(1).toString
  }
}

object permissionMultiplication extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "*"
  override val signature = new DomainFunctionSignature(DataTypeSequence(permissionType, permissionType), permissionType)(noLocation)
  override val domain = permissionDomain

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "*" + ts(1).toString
  }
}

object permissionIntegerMultiplication extends DomainFunction {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "*"
  override val signature = new DomainFunctionSignature(DataTypeSequence(integerType, permissionType), permissionType)(noLocation)
  override val domain = permissionDomain

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "*" + ts(1).toString
  }
}

///////////////////////////////////////////////////////////////////////////
object permissionLE extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "<="
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionLT extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "<"
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "<" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGE extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = ">="
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGT extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = ">"
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + ">" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionEQ extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "=="
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "==" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionNE extends DomainPredicate {
  override val comment = Nil
  override val sourceLocation = noLocation
  override val name = "!="
  override val signature = new DomainPredicateSignature(DataTypeSequence(permissionType, permissionType))(noLocation)
  override lazy val domain = permissionDomain

  override def toString(ts: TermSequence) = {
    require(ts.length == 2)
    ts(0).toString + "!=" + ts(1).toString
  }

  override def substitute(ts: TypeVariableSubstitution) = this

  private[sil] override def substituteI(ts: TypeVariableSubstitution) = this
}
