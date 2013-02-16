package semper.sil.ast

import utility.Consistency

/** A SIL program. */
// TODO consistency checks
case class Program(name: String, domains: Seq[Domain], fields: Seq[Field], functions: Seq[Function], predicates: Seq[Predicate], methods: Seq[Method])
                  (val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed

/** Common ancestor for members of a program. */
sealed trait Member extends Node with Positioned with Infoed {
  def name: String
}

/** Something with formal arguments. */
trait Callable {
  require(Consistency.noDuplicates(formalArgs))
  def formalArgs: Seq[LocalVar]
  def name: String
}

/** Common ancestor for functions and domain functions */
trait FuncLike extends Callable with Typed


/** A member with a contract. */
sealed trait Contracted extends Member {
  require(pres.forall(_.typ isSubtype Bool))
  require(posts.forall(_.typ isSubtype Bool))
  def pres: Seq[Exp]
  def posts: Seq[Exp]
}

/** A method declaration. */
case class Method(name: String, formalArgs: Seq[LocalVar], formalReturns: Seq[LocalVar], pres: Seq[Exp], posts: Seq[Exp], locals: Seq[LocalVar], private var _body: Stmt)
                 (val pos: Position = NoPosition, val info: Info = NoInfo) extends Callable with Contracted {
  require(Consistency.noDuplicates(formalArgs ++ formalReturns ++ locals))
  def body = _body
}

/** A common trait for locations (fields and predicates). */
sealed trait Location extends Member

/** A field declaration. */
case class Field(name: String)(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends Location with Typed

/** A predicate declaration. */
case class Predicate(name: String, var body: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Location

/** A function declaration */
case class Function(name: String, formalArgs: Seq[LocalVar], pres: Seq[Exp], posts: Seq[Exp], private var _exp: Exp)(val typ: Type, val pos: Position = NoPosition, val info: Info = NoInfo) extends FuncLike with Contracted {
  require(_exp == null || (_exp.typ isSubtype typ))
  def exp = _exp
  def exp_=(e: Exp) = {
    require(e.typ isSubtype typ)
    _exp = e
  }
}
