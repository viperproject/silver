package semper.sil.parser

import org.kiama.util.Messaging.message
import org.kiama.util.Messaging.messagecount
import org.kiama.util.Positioned

/**
 * A resolver and type-checker for the intermediate SIL AST.
 */
object Resolver {
  val names = NameAnalyser()

  def run(p: PProgram) {
    if (names.run(p)) {

    }
  }
}

/**
 * Performs type-checking and sets the type of all typed nodes.
 */
case class TypeChecker(names: NameAnalyser) {

  // some useful type aliases
  def Int = PPrimitiv("Int")
  def Bool = PPrimitiv("Bool")
  def Perm = PPrimitiv("Perm")
  def Ref = PPrimitiv("Ref")

  def check(p: PProgram) {
    p.methods map check
  }

  def check(m: PMethod) {
    check(m.body)
  }

  def check(stmt: PStmt) {
    stmt match {
      case PSeqn(ss) =>
        ss map check
      case PFold(e) =>
        check(e, Bool)
      case PUnfold(e) =>
        check(e, Bool)
      case PExhale(e) =>
        check(e, Bool)
      case PInhale(e) =>
        check(e, Bool)
      case PVarAssign(idnuse, rhs) =>
        names.definition(idnuse) match {
          case PLocalVarDecl(_, typ, _) =>
            check(rhs, typ)
          case _ =>
            message(stmt, "expected variable as lhs")
        }
      case PNewStmt(idnuse) =>
        names.definition(idnuse) match {
          case PLocalVarDecl(_, typ, _) =>
            ensure(typ == Ref, stmt, "target of new statement must be of Ref type")
          case _ =>
            message(stmt, "expected variable as lhs")
        }
      case PFieldAssign(field, rhs) => ???
      case PIf(cond, thn, els) =>
        check(cond, Bool)
        check(thn)
        check(els)
      case PWhile(cond, invs, body) =>
        check(cond, Bool)
        invs map (check(_, Bool))
        check(body)
      case PLocalVarDecl(idndef, typ, init) =>
        init match {
          case Some(i) => check(i, typ)
          case None =>
        }
      case PFreshReadPerm(vars, s) =>
        vars map {
          v =>
            names.definition(v) match {
              case PLocalVarDecl(_, typ, _) =>
                ensure(typ == Perm, v, "expected permission variable")
                check(v, typ)
              case _ =>
                message(v, "expected variable in fresh read permission block")
            }
        }
    }
  }

  /**
   * Type-check and resolve e and ensure that it has type expected.  If that is not the case, then an
   * error should be issued.
   */
  def check(e: PExp, expected: PType) {
    def setType(actual: PType) {
      if (actual == PUnkown()) {
        return // no error for unknown type (an error has already been issued)
      }
      if (expected == actual) {
        e.typ = expected
      } else {
        message(e, s"expected $expected, but got $actual")
      }
    }
    e match {
      case i@PIdnUse(name) =>
        names.definition(i) match {
          case PLocalVarDecl(_, typ, _) =>
            setType(typ)
          case _ =>
            message(i, "expected variable")
        }
      case PBinExp(left, op, right) =>
        op match {
          case "+" | "-" | "*" =>
            check(left, expected)
            check(right, expected)
            setType(expected)
          case "/" => ???
          case "%" => ???
          case "<" | "<=" | ">" | ">=" =>
          case "==" | "!=" =>
            val l = possibleTypes(left)
            val r = possibleTypes(right)
            (l intersect r) match {
              case Nil =>
                message(e, s"require same type for left/right side, but found (${possibleTypes(left)}} and ${possibleTypes(right)}})")
              case t :: ts =>
                check(left, t)
                check(right, t)
            }
            setType(Bool)
          case "&&" | "||" | "<==>" | "==>" =>
            check(left, Bool)
            check(right, Bool)
            setType(Bool)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, exp: PExp) => ???
      case PIntLit(i) =>
        setType(Int)
      case PResultLit() => ???
      case PBoolLit(b) =>
        setType(Bool)
      case PNullLit() =>
        setType(Ref)
      case PFieldAcc(rcv, idnuse) => ???
    }
  }

  /**
   * Returns the set of types that exp might possibly have.
   */
  def possibleTypes(exp: PExp): Seq[PType] = {
    exp match {
      case i@PIdnUse(name) =>
        names.definition(i) match {
        case PLocalVarDecl(_, typ, _) =>
          Seq(typ)
        case _ => Nil
      }
      case PBinExp(left, op, right) =>
        val l = possibleTypes(left)
        val r = possibleTypes(right)
        op match {
          case "+" | "-" | "*" =>
            (Seq(Int, Perm) intersect l) intersect r
          case "/" => ???
          case "%" => ???
          case "<" | "<=" | ">" | ">=" =>
            (Seq(Int, Perm) intersect l) intersect r
          case "==" | "!=" =>
            Seq(Bool)
          case "&&" | "||" | "<==>" | "==>" =>
            Seq(Bool)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, exp: PExp) => ???
      case PIntLit(i) => Seq(Int)
      case PResultLit() => ???
      case PBoolLit(b) => Seq(Bool)
      case PNullLit() => Seq(Ref)
      case PFieldAcc(rcv, idnuse) => ???
    }
  }

  /**
   * If b is false, report an error for node.
   */
  def ensure(b: Boolean, node: Positioned, msg: String) {
    if (!b) message(node, msg)
  }
}

/**
 * Resolves identifiers to their declaration.
 */
case class NameAnalyser() {

  def definition(idnuse: PIdnUse) = {
    idnMap.get(idnuse.name).get.asInstanceOf[RealEntity]
  }

  private val idnMap = collection.mutable.HashMap[String, Entity]()

  def run(p: PProgram): Boolean = {
    // find all declarations
    p.visit {
      case i@PIdnDef(name) =>
        idnMap.get(name) match {
          case Some(MultipleEntity()) =>
            message(i, s"$name already defined.")
          case Some(e) =>
            message(i, s"$name already defined.")
            idnMap.put(name, MultipleEntity())
          case None =>
            val e = i.parent match {
              case decl: PProgram => decl
              case decl: PMethod => decl
              case decl: PLocalVarDecl => decl
              case decl: PFormalArgDecl => decl
              case decl: PField => decl
              case decl: PDomain => decl
              case _ => sys.error(s"unexpected parent of identifier: ${i.parent}")
            }
            idnMap.put(name, e)
        }
      case _ =>
    }
    // check all identifier uses
    p visit {
      case i@PIdnUse(name) =>
        idnMap.getOrElse(name, UnknownEntity()) match {
          case UnknownEntity() =>
            message(i, s"$name not defined.")
          case _ =>
        }
      case _ =>
    }
    messagecount == 0
  }
}
