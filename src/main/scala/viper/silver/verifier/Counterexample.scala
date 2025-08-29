package viper.silver.verifier
import viper.silver.ast
import viper.silver.ast.{AbstractLocalVar, Exp, Type, Resource}

/**
  * Classes used for to build "intermediate" and "extended" counterexamples.
  */

case class StoreCounterexample(storeEntries: Seq[StoreEntry]) {
  override lazy val toString = storeEntries.map(x => x.toString).mkString("", "\n", "\n")
  lazy val asMap: Map[String, CEValue] = storeEntries.map(se => (se.id.name, se.entry)).toMap
}

case class StoreEntry(id: AbstractLocalVar, entry: CEValue) {
  override lazy val toString = {
    entry match {
      case CEVariable(_, _, _) => s"Variable Name: ${id.name}, Value: ${entry.value.toString}, Type: ${id.typ.toString}"
      case CESequence(name, length, entries, sequence, memberTypes) => s"Collection variable \"${id.name}\" of type ${id.typ.toString} with ${length} entries:${entries.map { case (k, v) => s"\n $v at index ${k.toString()}" }.mkString}"
      case CESet(name, length, entries, sequence, memberTypes) => s"Collection variable \"${id.name}\" of type ${id.typ.toString} with ${length} entries:${entries.map { case (k, true) => s"\n $k" }.mkString}"
      case CEMultiset(name, length, entries, memberTypes) => s"Collection variable \"${id.name}\" of type ${id.typ.toString} with ${length} entries:${entries.foreach { case (k, v) => s"\n ${v.toString} at index $k" }}"
    }
  }
}

case class HeapCounterexample(heapEntries: Seq[(Resource, FinalHeapEntry)]) {
  var finalString = ""
  var containsQP = false
  heapEntries.foreach { case (re,he) => if (he.entryType == QPFieldType || he.entryType == QPPredicateType || he.entryType == QPMagicWandType) containsQP = true}
  if (containsQP)
    finalString ++= "The heap contains Quantified Permissions. Thus, we might own some perm which are not presented in the Counterexample.\n"
  heapEntries.foreach { se => finalString ++= se._2.toString ++ "\n" }
  override lazy val toString = finalString
}

sealed trait FinalHeapEntry {
  val entryType : HeapEntryType
}

case class FieldFinalEntry(ref: String, field: String, entry: CEValue, perm: Option[Rational], typ: Type, het: HeapEntryType) extends FinalHeapEntry {
  val entryType = het
  override lazy val toString = s"Field Entry: $ref.$field --> (Value: ${entry.value.toString}, Type: ${typ}, Perm: ${perm.getOrElse("#undefined").toString})"
}

case class PredFinalEntry(name: String, args: Seq[String], perm: Option[Rational], insidePredicate: Option[scala.collection.immutable.Map[Exp, ModelEntry]], het: HeapEntryType) extends FinalHeapEntry {
  val entryType = het
  override lazy val toString = s"Predicate Entry: $name(${args.mkString("", ", ", ")")} --> (Perm: ${perm.getOrElse("#undefined").toString}) ${if (insidePredicate.isDefined && !insidePredicate.get.isEmpty) insidePredicate.get.toSeq.map(x => s"${x._1} --> ${x._2}")mkString("{\n   ", "\n   ", "\n}") else ""}"
}

case class WandFinalEntry(name: String, left: Exp, right: Exp, args: Map[String, String], perm: Option[Rational], het: HeapEntryType) extends FinalHeapEntry {
  val entryType = het
  override lazy val toString = s"Magic Wand Entry: $name --> (Left: ${left.toString}, Right: ${right.toString}, Perm: ${perm.getOrElse("#undefined").toString})"
}

sealed trait CEValue {
  val id : String
  val value : Any
  val valueType : Option[ast.Type]
}

object CEValueOnly {
  def apply(value: ModelEntry, typ: Option[ast.Type]): CEValue = CEVariable("#undefined", value, typ)
  def unapply(ce: CEValue): Option[(ModelEntry, Option[ast.Type])] = ce match {
    case CEVariable(_, entryValue, typ) => Some((entryValue, typ))
    case _ => None
  }
}

case class CEVariable(name: String, entryValue: ModelEntry, typ: Option[Type]) extends CEValue {
  val id = name
  val value = entryValue
  val valueType = typ
  override lazy val toString = s"Variable Name: ${name}, Value: ${value.toString}, Type: ${typ.getOrElse("None").toString}"
}

case class CESequence(name: String, length: BigInt, entries: Map[BigInt, String], sequence: Seq[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = sequence
  val valueType = memberTypes
  val size = length
  val inside = entries
  override lazy val toString = {
    var finalString = s"$name with size ${size.toString()} with entries:"
    for ((k,v) <- inside)
      finalString ++= s"\n $v at index ${k.toString()}"
    finalString
  }
}

case class CESet(name: String, cardinality: BigInt, containment: Map[String, Boolean], set: Set[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = set
  val valueType = memberTypes
  val size = cardinality
  val inside = containment
  override lazy val toString = s"Set $name of size ${size.toString()} with entries: ${inside.filter(x => x._2).map(x => x._1).mkString("{", ", ", "}")}"
}

case class CEMultiset(name: String, cardinality: BigInt, containment: scala.collection.immutable.Map[String, Int], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = containment
  val valueType = memberTypes
  val size = cardinality
  override lazy val toString = {
    var finalString = s"Multiset $name of size ${size.toString()} with entries:"
    for ((k, v) <- containment)
      finalString ++= s"\n $k occurs ${v.toString} time"
    finalString
  }
}

case class BasicHeap(basicHeapEntries: Set[BasicHeapEntry]) {
  override lazy val toString = basicHeapEntries.map(x => x.toString).mkString("", "\n", "")
}

case class BasicHeapEntry(reference: Seq[String], field: Seq[String], valueID: String, perm: Option[Rational], het: HeapEntryType, insidePredicate: Option[scala.collection.immutable.Map[Exp, ModelEntry]]) {
  override lazy val toString = {
    het match {
      case PredicateType =>
        println(insidePredicate.get.toString())
        s"Heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Permission: ${perm.getOrElse("None")}) ${if (insidePredicate.isDefined && !insidePredicate.get.isEmpty) insidePredicate.get.toSeq.map(x => s"${x._1} --> ${x._2}")mkString("{\n   ", "\n   ", "\n}") else ""}"
      case _ => s"Heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Value: $valueID, Permission: ${perm.getOrElse("None")})"
    }
  }
}

case class BasicDomainEntry(name: String, types: Seq[ast.Type], functions: Seq[BasicFunction]) {
  override def toString: String = s"domain $valueName{\n ${functions.map(_.toString()).mkString("\n")}\n}"
  val valueName: String = s"$name${printTypes()}"
  private def printTypes(): String =
    if (types.isEmpty) ""
    else types.map(printType).mkString("[", ", ", "]")
  private def printType(t: ast.Type): String = t match {
    case ast.TypeVar(x) => x
    case _ => t.toString()
  }
}


case class BasicFunction(fname: String, argtypes: Seq[ast.Type], returnType: ast.Type, options: Map[Seq[String], String], default: String) {
  override def toString: String = {
    if (options.nonEmpty)
      s"$fname${argtypes.mkString("(", ",", ")")}:${returnType}{\n" + options.map(o => "    " + o._1.mkString(" ") + " -> " + o._2).mkString("\n") + "\n    else -> " + default + "\n}"
    else
      s"$fname{\n    " + default + "\n}"
  }
}

sealed trait HeapEntryType
case object FieldType extends HeapEntryType
case object PredicateType extends HeapEntryType
case object QPFieldType extends HeapEntryType
case object QPPredicateType extends HeapEntryType
case object MagicWandType extends HeapEntryType
case object QPMagicWandType extends HeapEntryType

/*
  Helper class for permissions
 */

final class Rational(n: BigInt, d: BigInt) extends Ordered[Rational] {
  require(d != 0, "Denominator of Rational must not be 0.")

  private val g = n.gcd(d)
  val numerator: BigInt = n / g * d.signum
  val denominator: BigInt = d.abs / g

  def +(that: Rational): Rational = {
    val newNum = this.numerator * that.denominator + that.numerator * this.denominator
    val newDen = this.denominator * that.denominator
    Rational(newNum, newDen)
  }
  def -(that: Rational): Rational = this + (-that)
  def unary_- = Rational(-numerator, denominator)
  def abs = Rational(numerator.abs, denominator)
  def signum = Rational(numerator.signum, 1)

  def *(that: Rational): Rational = Rational(this.numerator * that.numerator, this.denominator * that.denominator)
  def /(that: Rational): Rational = this * that.inverse
  def inverse = Rational(denominator, numerator)

  def compare(that: Rational) = (this.numerator * that.denominator - that.numerator * this.denominator).signum

  override def equals(obj: Any) = obj match {
    case that: Rational => this.numerator == that.numerator && this.denominator == that.denominator
    case _ => false
  }

  override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(n, d)

  override lazy val toString = s"$numerator/$denominator"
}

object Rational extends ((BigInt, BigInt) => Rational) {
  val zero = Rational(0, 1)
  val one = Rational(1, 1)

  def apply(numer: BigInt, denom: BigInt) = new Rational(numer, denom)

  def unapply(r: Rational) = Some(r.numerator, r.denominator)
}