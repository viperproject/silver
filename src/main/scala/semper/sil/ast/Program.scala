package semper.sil.ast

import utility.Consistency
import org.kiama.output._

/** A SIL program. */
// TODO consistency checks
case class Program(domains: Seq[Domain], fields: Seq[Field], functions: Seq[Function], predicates: Seq[Predicate], methods: Seq[Method])
                  (val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed

// --- Program members

/** A field declaration. */
case class Field(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Location with Typed {
  require(typ.isConcrete)
}

/** A predicate declaration. */
case class Predicate(name: String, formalArg: LocalVarDecl, private var _body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Location {
  if (body != null) Consistency.checkContract(body)
  def body = _body
  def body_=(b: Exp) {
    Consistency.checkContract(b)
    _body = b
  }
}

/** A method declaration. */
case class Method(name: String, formalArgs: Seq[LocalVarDecl], formalReturns: Seq[LocalVarDecl], private var _pres: Seq[Exp], private var _posts: Seq[Exp], private var _locals: Seq[LocalVarDecl], var body: Stmt)
                 (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with Callable with Contracted {
  require(noDuplicates)
  require((formalArgs ++ formalReturns) forall (_.typ.isConcrete))
  private def noDuplicates = Consistency.noDuplicates(formalArgs ++ Consistency.nullValue(locals, Nil) ++ Seq(LocalVar(name)(Bool)))
  def pres = _pres
  def pres_=(s: Seq[Exp]) {
    s map Consistency.checkContract
    _pres = s
  }
  def posts = _posts
  def posts_=(s: Seq[Exp]) {
    s map Consistency.checkContract
    _posts = s
  }
  def locals = _locals
  def locals_=(s: Seq[LocalVarDecl]) {
    _locals = s
    require(noDuplicates)
  }
}

/** A function declaration */
case class Function(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, private var _pres: Seq[Exp], private var _posts: Seq[Exp], private var _exp: Exp)
                   (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with FuncLike with Contracted {
  require(_exp == null || (_exp isSubtype typ))
  def pres = _pres
  def pres_=(s: Seq[Exp]) {
    s map Consistency.checkContract
    _pres = s
  }
  def posts = _posts
  def posts_=(s: Seq[Exp]) {
    s map Consistency.checkContract
    _posts = s
  }
  def exp = _exp /* TODO: [Malte] I suggest to rename 'exp' to 'body' since the latter is more descriptive. */
  def exp_=(e: Exp) {
    require(e isSubtype typ)
    _exp = e
  }
  
  /**
   * The result variable of this function (without position or info).
   */
  def result = Result()(typ)

  /**
   * Is this function recursive?
   */
  def isRecursive: Boolean = exp exists {
    case FuncApp(func, _) if name == func.name =>
  }
}


// --- Local variable declarations

/**
 * Local variable declaration.  Note that these are not statements in the AST, but
 * rather occur as part of a method, loop, function, etc.
 */
case class LocalVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed with Typed {
  require(Consistency.validUserDefinedIdentifier(name))

  /**
   * Returns a local variable of the same name and type as this declaration, without position or
   * information.
   */
  lazy val localVar = LocalVar(name)(typ)
}


// --- Domains and domain members

/** A user-defined domain. */
case class Domain(name: String, var _functions: Seq[DomainFunc], var _axioms: Seq[DomainAxiom], typVars: Seq[TypeVar] = Nil)
                 (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))
  def functions = _functions
  def functions_=(fs: Seq[DomainFunc]) {
    _functions = fs
  }
  def axioms = _axioms
  def axioms_=(as: Seq[DomainAxiom]) {
    _axioms = as
  }
}

/** A domain axiom. */
case class DomainAxiom(name: String, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainMember {
  require(exp isSubtype Bool)
}

/** Domain function which is not a binary or unary operator. */
case class DomainFunc(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, unique: Boolean = false)
                     (val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractDomainFunc with DomainMember {
  require(!unique || formalArgs.isEmpty, "Only constants, i.e. nullary domain functions can be unique.")
}


// --- Common functionality

/** Common ancestor for members of a program. */
sealed trait Member extends Node with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))
  def name: String

  // we override the definition of hashCode/equals to avoid unbounded recursion
  override def hashCode = name.hashCode
  override def equals(o: Any) = o match {
    case m: Member => name == m.name
    case _ => false
  }
}

/** Common ancestor for domain members. */
sealed trait DomainMember extends Node with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))
  def name: String

  // we override the definition of hashCode/equals to avoid unbounded recursion
  override def hashCode = name.hashCode
  override def equals(o: Any) = o match {
    case m: Member => name == m.name
    case _ => false
  }
}

/** Common ancestor for things with formal arguments. */
sealed trait Callable {
  require(Consistency.noDuplicates(formalArgs))
  def formalArgs: Seq[LocalVarDecl]
  def name: String
}

/** Common ancestor for functions and domain functions */
sealed trait FuncLike extends Callable with Typed

/** A member with a contract. */
sealed trait Contracted extends Member {
  if (pres != null) pres map Consistency.checkContract
  if (posts != null) posts map Consistency.checkContract
  def pres: Seq[Exp]
  def posts: Seq[Exp]
}

/** A common trait for locations (fields and predicates). */
sealed trait Location extends Member

/** Common superclass for domain functions and binary/unary operators. */
sealed trait AbstractDomainFunc extends FuncLike with Positioned with Infoed


// --- Built-in domain functions and operators

/** Built-in domain functions  */
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
/** Domain functions with return type permission. */
sealed trait PermDomainFunc extends AbstractDomainFunc {
  lazy val typ = Perm
}

/** Domain functions that represent built-in binary operators */
sealed trait BinOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("left", leftTyp)(), LocalVarDecl("right", rightTyp)())
  def leftTyp: Type
  def rightTyp: Type
}

/** Left associative operator. */
sealed trait LeftAssoc {
  lazy val fixity = Infix (LeftAssoc)
}

/** Domain functions that represent built-in binary operators where both arguments are integers. */
sealed trait IntBinOp extends BinOp {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Domain functions that represent built-in binary operators where both arguments are booleans. */
sealed trait BoolBinOp extends BinOp {
  lazy val leftTyp = Bool
  lazy val rightTyp = Bool
}

/** Domain functions that represent built-in binary operators where both arguments are permissions. */
sealed trait PermBinOp extends BinOp {
  lazy val leftTyp = Perm
  lazy val rightTyp = Perm
}

/** Domain functions that represent built-in unary operators */
sealed trait UnOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("exp", expTyp)())
  def expTyp: Type
}

/** Common interface for sum operators. */
sealed abstract class SumOp(val op: String) extends LeftAssoc {
  lazy val priority = 12
}
/** Common interface for product operators. */
sealed abstract class ProdOp(val op: String) extends LeftAssoc {
  lazy val priority = 11
}
/** Common interface for relational operators. */
sealed abstract class RelOp(val op: String) extends BoolDomainFunc {
  lazy val priority = 13
  lazy val fixity = Infix (NonAssoc)
}

// Arithmetic integer operators
case object AddOp extends SumOp("+") with IntBinOp with IntDomainFunc
case object SubOp extends SumOp("-") with IntBinOp with IntDomainFunc
case object MulOp extends ProdOp("*") with IntBinOp with IntDomainFunc
case object DivOp extends ProdOp("\\") with IntBinOp with IntDomainFunc
case object ModOp extends ProdOp("%") with IntBinOp with IntDomainFunc

// Arithmetic permission operators
case object PermAddOp extends SumOp("+") with PermBinOp with PermDomainFunc
case object PermSubOp extends SumOp("-") with PermBinOp with PermDomainFunc
case object PermMulOp extends ProdOp("*") with PermBinOp with PermDomainFunc
case object IntPermMulOp extends ProdOp("*") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Perm
}
case object FracOp extends ProdOp("/") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Integer negation. */
case object NegOp extends UnOp with IntDomainFunc {
  lazy val expTyp = Int
  lazy val op = "-"
  lazy val priority = 10
  lazy val fixity = Prefix
}

// Integer comparison operators
case object LtOp extends RelOp("<") with IntBinOp
case object LeOp extends RelOp("<=") with IntBinOp
case object GtOp extends RelOp(">") with IntBinOp
case object GeOp extends RelOp(">=") with IntBinOp

// Permission comparison operators
case object PermLtOp extends RelOp("<") with PermBinOp
case object PermLeOp extends RelOp("<=") with PermBinOp
case object PermGtOp extends RelOp(">") with PermBinOp
case object PermGeOp extends RelOp(">=") with PermBinOp

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

/** Boolean negation. */
case object NotOp extends UnOp with BoolDomainFunc {
  lazy val expTyp = Bool
  lazy val op = "!"
  lazy val priority = 1
  lazy val fixity = Prefix
}
