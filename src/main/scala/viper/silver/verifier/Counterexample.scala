package viper.silver.verifier
import viper.silver.ast
import viper.silver.ast.{AbstractLocalVar, Exp, Type, Resource}

/**
  * Classes used to build counterexamples. Two layers are distinguished:
  *
  *   - a "raw" counterexample ([[RawCounterexample]]) that contains all information in a simple,
  *     machine-readable form, keyed by the backend-internal (SMT/Boogie) identifiers, and
  *   - a "resolved" counterexample ([[ResolvedCounterexample]]) that makes the raw one
  *     human-readable, e.g. by binding heap resources to their AST nodes and translating internal
  *     value identifiers to the program variables that denote them.
  *
  * Values are represented as ordinary Viper AST expressions ([[ast.Exp]]). Literals that have no
  * ordinary Viper representation use the dedicated counterexample literals [[ast.RefLit]] (a
  * concrete reference) and [[ast.BackendValueLit]] (an otherwise opaque backend value).
  */

trait RawCounterexample {
  val basicVariables: Seq[CEVariable]
  val allSequences: Seq[CECollection]
  val allSets: Seq[CECollection]
  val allMultisets: Seq[CECollection]
  lazy val allCollections: Seq[CECollection] = allSequences ++ allSets ++ allMultisets
  def allRawHeaps: Seq[(String, RawHeap)]

  val domainEntries: Seq[BasicDomainEntry]
  val nonDomainFunctions: Seq[BasicFunctionEntry]
}

trait ResolvedCounterexample {
  val rawCE: RawCounterexample
  val ceStore: StoreCounterexample
  val ceHeaps: Seq[(String, HeapCounterexample)]
  lazy val heapMap = ceHeaps.toMap
  val domainEntries: Seq[BasicDomainEntry]
  val functionEntries: Seq[BasicFunctionEntry]
  lazy val domainsAndFunctions = domainEntries ++ functionEntries
}

/**
  * Helper for turning a backend value string (plus an optional Viper type) into the AST expression
  * that represents it in a counterexample.
  */
object CounterexampleValue {
  /** SMT solvers represent negative integers as an application, e.g. "(- 1)". */
  private val smtNegative = """^\(\s*-\s*(\d+)\s*\)$""".r

  /** Parses an integer from its backend string representation, handling SMT-style negatives. */
  def parseInt(value: String): Option[BigInt] = {
    val trimmed = value.trim
    try Some(BigInt(trimmed)) catch {
      case _: NumberFormatException => trimmed match {
        case smtNegative(digits) => Some(-BigInt(digits))
        case _ => None
      }
    }
  }

  def parseBool(value: String): Option[Boolean] = value.trim.toLowerCase match {
    case "true" => Some(true)
    case "false" => Some(false)
    case _ => None
  }

  /**
    * Infers a literal from a backend value string when no Viper type is available. The element
    * types of collections are not always known, so this makes value comparison robust: an integer
    * or boolean value becomes the corresponding literal regardless of whether the type was inferred.
    */
  def inferLiteral(value: String): ast.Exp =
    parseInt(value).map(i => ast.IntLit(i)(): ast.Exp)
      .orElse(parseBool(value).map(b => ast.BoolLit(b)()))
      .getOrElse(ast.BackendValueLit(value, ast.InternalType)())

  def literal(value: String, typ: Option[ast.Type]): ast.Exp = typ match {
    case Some(ast.Int) =>
      parseInt(value).map(i => ast.IntLit(i)()).getOrElse(ast.BackendValueLit(value, ast.Int)())
    case Some(ast.Bool) =>
      parseBool(value).map(b => ast.BoolLit(b)()).getOrElse(ast.BackendValueLit(value, ast.Bool)())
    case Some(ast.Ref) => ast.RefLit(value)()
    case Some(t) => ast.BackendValueLit(value, t)()
    case None => inferLiteral(value)
  }
}

case class StoreCounterexample(storeEntries: Seq[StoreEntry]) {
  override lazy val toString = storeEntries.map(x => x.toString).mkString("", "\n", "\n")
  lazy val asMap: Map[String, ast.Exp] = storeEntries.map(se => (se.id.name, se.entry)).toMap
}

case class StoreEntry(id: AbstractLocalVar, entry: ast.Exp) {
  override lazy val toString = s"Variable Name: ${id.name}, Value: ${entry.toString}, Type: ${id.typ.toString}"
}

case class HeapCounterexample(heapEntries: Seq[(Resource, ResolvedHeapEntry)]) {
  var finalString = ""
  var containsQP = false
  heapEntries.foreach { case (re,he) => if (he.entryType == QPFieldType || he.entryType == QPPredicateType || he.entryType == QPMagicWandType) containsQP = true}
  if (containsQP)
    finalString ++= "The heap contains quantified permissions. Thus, we might own some permissions which are not shown in the counterexample.\n"
  heapEntries.foreach { se => finalString ++= se._2.toString ++ "\n" }
  override lazy val toString = finalString
}

sealed trait ResolvedHeapEntry {
  val entryType : HeapEntryType
}

case class FieldResolvedEntry(ref: String, field: String, entry: ast.Exp, perm: Option[Rational], typ: Type, het: HeapEntryType) extends ResolvedHeapEntry {
  val entryType = het
  override lazy val toString = s"Field Entry: $ref.$field --> (Value: ${entry.toString}, Type: ${typ}, Perm: ${perm.getOrElse("#undefined").toString})"
}

case class PredResolvedEntry(name: String, args: Seq[Exp], perm: Option[Rational], insidePredicate: Option[scala.collection.immutable.Map[Exp, ModelEntry]], het: HeapEntryType) extends ResolvedHeapEntry {
  val entryType = het
  override lazy val toString = s"Predicate Entry: $name(${args.mkString("", ", ", ")")} --> (Perm: ${perm.getOrElse("#undefined").toString}) ${if (insidePredicate.isDefined && !insidePredicate.get.isEmpty) insidePredicate.get.toSeq.map(x => s"${x._1} --> ${x._2}")mkString("{\n   ", "\n   ", "\n}") else ""}"
}

case class WandResolvedEntry(name: String, left: Exp, right: Exp, args: Seq[Exp], perm: Option[Rational], het: HeapEntryType) extends ResolvedHeapEntry {
  val entryType = het
  override lazy val toString = s"Magic Wand Entry: $name(${args.map(_.toString).mkString(", ")}) --> (Left: ${left.toString}, Right: ${right.toString}, Perm: ${perm.getOrElse("#undefined").toString})"
}

object WandResolvedEntry {
  /**
    * Builds a wand entry for the magic-wand structure `mw`, substituting the instance's argument
    * values (`argValues`, given in the order of `subexpressionsToEvaluate`) into the wand's two
    * sides. The substituted values are the same counterexample literals used elsewhere in the model.
    */
  def fromStructure(name: String, mw: ast.MagicWandStructure.MagicWandStructure, argValues: Seq[String],
                    perm: Option[Rational], het: HeapEntryType, program: ast.Program): WandResolvedEntry = {
    val structure = mw.structure(program, true)
    val holes = structure.subexpressionsToEvaluate(program)
    val argExps: Seq[ast.Exp] = holes.zip(argValues).map { case (hole, v) => CounterexampleValue.literal(v, Some(hole.typ)) }
    val repl: scala.collection.immutable.Map[ast.Node, ast.Node] =
      scala.collection.immutable.Map.from(holes.zip(argExps): Iterable[(ast.Node, ast.Node)])
    val transformed = structure.replace(repl)
    WandResolvedEntry(name, transformed.left, transformed.right, argExps, perm, het)
  }
}

/**
  * A local (store) variable together with its value.
  * `value` is an AST expression (a literal such as [[ast.IntLit]]/[[ast.RefLit]], or a collection
  * expression such as [[ast.ExplicitSeq]]).
  */
case class CEVariable(name: String, value: ast.Exp, typ: Option[Type]) {
  override lazy val toString = s"Variable Name: ${name}, Value: ${value.toString}, Type: ${typ.getOrElse("None").toString}"
}

/**
  * A collection value (sequence, set or multiset) reconstructed from the model, together with its
  * backend-internal identifier `id`. `value` is the corresponding AST collection expression
  * (e.g. [[ast.ExplicitSeq]]); `id` is used to link store variables and heap values to the
  * collection they refer to.
  */
case class CECollection(id: String, value: ast.Exp) {
  override lazy val toString = s"${id} = ${value.toString}"
}

case class RawHeap(rawHeapEntries: Set[RawHeapEntry]) {
  override lazy val toString = rawHeapEntries.map(x => x.toString).mkString("", "\n", "")
}

case class RawHeapEntry(reference: Seq[String], field: Seq[String], valueID: String, perm: Option[Rational], het: HeapEntryType, insidePredicate: Option[scala.collection.immutable.Map[Exp, ModelEntry]]) {
  override lazy val toString = {
    het match {
      case PredicateType =>
        s"Heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Permission: ${perm.getOrElse("None")}) ${if (insidePredicate.isDefined && !insidePredicate.get.isEmpty) insidePredicate.get.toSeq.map(x => s"${x._1} --> ${x._2}")mkString("{\n   ", "\n   ", "\n}") else ""}"
      case _ => s"Heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Value: $valueID, Permission: ${perm.getOrElse("None")})"
    }
  }
}

case class BasicDomainEntry(name: String, types: Seq[ast.Type], functions: Seq[BasicFunctionEntry]) {
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


case class BasicFunctionEntry(fname: String, argtypes: Seq[ast.Type], returnType: ast.Type, options: Map[Seq[String], String], default: String) {
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
