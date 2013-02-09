package semper.sil.ast

import org.kiama.output._
import org.kiama.output.Infix

/** A user-defined domain. */
case class Domain(name: String, functions: Seq[DomainFunc], axioms: Seq[DomainAxiom], typVars: Seq[TypeVar] = Nil)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed

trait DomainAxiom {
  require(exp.typ == Bool)
  def name: String
  def exp: Exp
}

/** Common superclass for Domain functions and binary/unary operators. */
sealed trait AbstractDomainFunc extends FuncLike with Positioned with Infoed

/** Domain function which is not a binary or unary operator. */
case class DomainFunc(name: String, formalArgs: Seq[LocalVar])(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractDomainFunc

/** Built in domain functions  */
sealed trait BuiltinDomainFunc extends AbstractDomainFunc {
  lazy val info = NoInfo
  lazy val pos = NoPosition
}

/** Domain functions which are written as infix or prefix operators. */
sealed trait Op extends AbstractDomainFunc with BuiltinDomainFunc {
  lazy val name = op
  def op: String
  def fixity: Fixity
  def priority: Int
}

/** Domain functions with return type integer. */
sealed trait IntDomainFunc extends AbstractDomainFunc {
  lazy val typ = Int
}
/** Domain functions with return type boolean. */
sealed trait BoolDomainFunc extends AbstractDomainFunc {
  lazy val typ = Bool
}

/** Domain functions that represent built-in binary operators */
sealed trait BinOp extends Op {
  lazy val formalArgs = List(LocalVar("left")(leftTyp), LocalVar("right")(rightTyp))
  def leftTyp: Type
  def rightTyp: Type
}

/** Left associative expression. */
sealed trait LeftAssoc {
  lazy val fixity = Infix (LeftAssoc)
}

/** Domain functions that represent built-in binary operators where both arguments are integers */
sealed trait IntBinOp extends BinOp {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Domain functions that represent built-in binary operators where both arguments are booleans */
sealed trait BoolBinOp extends BinOp {
  lazy val leftTyp = Bool
  lazy val rightTyp = Bool
}

/** Domain functions that represent built-in unary operators */
sealed trait UnOp extends Op {
  lazy val formalArgs = List(LocalVar("exp")(expTyp))
  def expTyp: Type
}

/** Common interface for sum expressions. */
sealed abstract class SumOp(val op: String) extends IntBinOp with IntDomainFunc with LeftAssoc {
  lazy val priority = 12
}
/** Common interface for product expressions. */
sealed abstract class ProdOp(val op: String) extends IntBinOp with IntDomainFunc with LeftAssoc {
  lazy val priority = 11
}
/** Common interface for relational expressions. */
sealed abstract class RelOp(val op: String) extends IntBinOp with BoolDomainFunc {
  lazy val priority = 13
  lazy val fixity = Infix (NonAssoc)
}

// Arithmetic expressions
case object PlusOp extends SumOp("+")
case object MinusOp extends SumOp("-")
case object TimesOp extends ProdOp("*")
case object DividedOp extends ProdOp("/")
case object ModuloOp extends ProdOp("%")

/** Integer negation. */
case object NegOp extends UnOp with IntDomainFunc {
  lazy val expTyp = Int
  lazy val op = "-"
  lazy val priority = 10
  lazy val fixity = Prefix
}

// Integer comparison expressions
case object LtOp extends RelOp("<")
case object LeOp extends RelOp("<=")
case object GtOp extends RelOp(">")
case object GeOp extends RelOp(">=")
case object EqOp extends RelOp("==")
case object NeOp extends RelOp("!=")

// Boolean expressions
/** Boolean or. */
case object OrOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "||"
  lazy val priority = 3
}

/** Boolean and. */
case object AndOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "&&"
  lazy val priority = 2
}

/** Boolean implication. */
case object ImpliesOp extends BoolBinOp with BoolDomainFunc {
  lazy val op = "==>"
  lazy val priority = 4
  lazy val fixity = Infix (RightAssoc)
}

/** Boolean equivalence. */
case object EquivOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "<==>"
  lazy val priority = 5
}

/** Boolean negation. */
case object NotOp extends UnOp with BoolDomainFunc {
  lazy val expTyp = Bool
  lazy val op = "!"
  lazy val priority = 1
  lazy val fixity = Prefix
}
