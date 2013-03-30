package semper.sil.parser

import org.kiama.util.Messaging.message
import org.kiama.util.Messaging.messagecount
import org.kiama.util.Positioned

/**
 * A resolver and type-checker for the intermediate SIL AST.
 */
case class Resolver(p: PProgram) {
  val names = NameAnalyser()
  val typechecker = TypeChecker(names)

  def run: Boolean = {
    if (names.run(p)) {
      if (typechecker.run(p)) {
        return true
      }
    }
    false
  }
}

/**
 * Performs type-checking and sets the type of all typed nodes.
 */
case class TypeChecker(names: NameAnalyser) {

  import TypeHelper._

  var curMember: PMember = null

  def run(p: PProgram): Boolean = {
    check(p)
    messagecount == 0
  }

  def check(p: PProgram) {
    p.domains map check
    p.fields map check
    p.functions map check
    p.predicates map check
    p.methods map check
  }

  def checkMember(m: PMember)(fcheck: => Unit) {
    curMember = m
    fcheck
    curMember = null
  }

  def check(m: PMethod) {
    checkMember(m) {
      (m.formalArgs ++ m.formalReturns) map (a => check(a.typ))
      m.pres map (check(_, Bool))
      m.posts map (check(_, Bool))
      check(m.body)
    }
  }

  def check(f: PFunction) {
    checkMember(f) {
      check(f.typ)
      f.formalArgs map (a => check(a.typ))
      check(f.typ)
      f.pres map (check(_, Bool))
      f.posts map (check(_, Bool))
      check(f.exp, f.typ)
    }
  }

  def check(p: PPredicate) {
    checkMember(p) {
      check(p.formalArg.typ)
      ensure(p.formalArg.typ == Ref, p.formalArg, "expected Ref the type of the argument")
      check(p.body, Bool)
    }
  }

  def check(f: PField) {
    checkMember(f) {
      check(f.typ)
    }
  }

  def check(d: PDomain) {
    checkMember(d) {
      d.funcs map check
      d.axioms map check
    }
  }

  def check(a: PAxiom) {
    check(a.exp, Bool)
  }

  def check(f: PDomainFunction) {
    check(f.typ)
    f.formalArgs map (a => check(a.typ))
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
      case PAssert(e) =>
        check(e, Bool)
      case PInhale(e) =>
        check(e, Bool)
      case PVarAssign(idnuse, rhs) =>
        names.definition(curMember)(idnuse) match {
          case PLocalVarDecl(_, typ, _) =>
            check(idnuse, typ)
            check(rhs, typ)
          case PFormalArgDecl(_, typ) =>
            check(idnuse, typ)
            check(rhs, typ)
          case _ =>
            message(stmt, "expected variable as lhs")
        }
      case PNewStmt(idnuse) =>
        names.definition(curMember)(idnuse) match {
          case PLocalVarDecl(_, typ, _) =>
            check(idnuse, Ref)
          case PFormalArgDecl(_, typ) =>
            check(idnuse, Ref)
          case _ =>
            message(stmt, "expected variable as lhs")
        }
      case PFieldAssign(field, rhs) =>
        names.definition(curMember)(field.idnuse) match {
          case PField(_, typ) =>
            check(field, typ)
            check(rhs, typ)
          case _ =>
            message(stmt, "expected a field as lhs")
        }
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
            names.definition(curMember)(v) match {
              case PLocalVarDecl(_, typ, _) =>
                check(v, Perm)
              case PFormalArgDecl(_, typ) =>
                check(v, Perm)
              case _ =>
                message(v, "expected variable in fresh read permission block")
            }
        }
    }
  }

  def check(typ: PType) {
    typ match {
      case PPredicateType() =>
        sys.error("unexpected use of internal typ")
      case PPrimitiv(_) =>
      case PTypeVar(n) =>
        message(typ, "expected concrete type, but found type variable")
      case PDomainType(domain, args) =>
        args map check
        names.definition(curMember)(domain) match {
          case PDomain(name, typVars, _, _) => ???
          case _ =>
            message(typ, "expected domain")
        }
      case PUnkown() =>
        message(typ, "expected concrete type, but found unknown typ")
    }
  }

  /**
   * Type-check and resolve e and ensure that it has type expected.  If that is not the case, then an
   * error should be issued.
   *
   * null can be passed for expected, if any type is fine.
   */
  def check(exp: PExp, expected: PType) {
    def setType(actual: PType) {
      if (actual == PUnkown()) {
        return // no error for unknown type (an error has already been issued)
      }
      if (expected == null || expected == actual) {
        exp.typ = expected
      } else {
        message(exp, s"expected $expected, but got $actual")
      }
    }
    exp match {
      case i@PIdnUse(name) =>
        names.definition(curMember)(i) match {
          case PLocalVarDecl(_, typ, _) =>
            setType(typ)
          case PFormalArgDecl(_, typ) =>
            setType(typ)
          case PField(_, typ) =>
            setType(typ)
          case x =>
            message(i, s"expected variable or field, but got $x")
            setType(expected) // suppress further warnings
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
            val l = possibleTypes(left)
            val r = possibleTypes(right)
            val t = l intersect r
            if (t.size > 0) {
              check(left, t(0))
              check(right, t(0))
            } else {
              message(exp, s"expected two Ints or two Perms, but found $l and $r")
            }
            setType(Bool)
          case "==" | "!=" =>
            val l = possibleTypes(left)
            val r = possibleTypes(right)
            (l intersect r) match {
              case Nil =>
                message(exp, s"require same type for left/right side, but found $l and $r")
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
      case PUnExp(op, e) =>
        op match {
          case "-" | "+" =>
            check(e, expected)
            setType(expected)
          case "!" =>
            check(e, expected)
            setType(Bool)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PIntLit(i) =>
        setType(Int)
      case r@PResultLit() =>
        curMember match {
          case PFunction(_, _, typ, _, _, _) =>
            setType(typ)
          case _ =>
            message(r, "'result' can only be used in functions")
            setType(expected) // suppress further warnings
        }
      case PBoolLit(b) =>
        setType(Bool)
      case PNullLit() =>
        setType(Ref)
      case PLocationAccess(rcv, idnuse) =>
        check(rcv, Ref)
        check(idnuse, expected)
      case fa@PFunctApp(func, args) =>
        names.definition(curMember)(func) match {
          case PFunction(_, formalArgs, typ, _, _, _) =>
            ensure(formalArgs.size == args.size, fa, "wrong number of arguments")
            (formalArgs zip args) foreach {
              case (formal, actual) =>
                check(actual, formal.typ)
            }
            setType(typ)
          case x =>
            message(func, s"expected function")
            setType(expected) // suppress further warnings
        }
      case PUnfolding(loc, e) =>
        check(loc, Pred)
        check(e, expected)
      case PExists(variable, e) =>
        check(variable.typ)
        check(e, Bool)
      case PForall(variable, e) =>
        check(variable.typ)
        check(e, Bool)
      case PCondExp(cond, thn, els) => ???
      case PCurPerm(loc) =>
        check(loc, null)
        setType(Perm)
      case PNoPerm() =>
        setType(Perm)
      case PFullPerm() =>
        setType(Perm)
      case PWildcard() =>
        setType(Perm)
      case PConcretePerm(a, b) =>
        setType(Perm)
      case PEpsilon() =>
        setType(Perm)
      case PAccPred(loc, perm) =>
        check(loc, null)
        check(perm, Perm)
    }
  }

  /**
   * Returns the set of types that exp might possibly have.
   */
  def possibleTypes(exp: PExp): Seq[PType] = {
    exp match {
      case i@PIdnUse(name) =>
        names.definition(curMember)(i) match {
          case PLocalVarDecl(_, typ, _) =>
            Seq(typ)
          case PFormalArgDecl(_, typ) =>
            Seq(typ)
          case PField(_, typ) =>
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
      case PUnExp(op, e) =>
        op match {
          case "-" => possibleTypes(e)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PIntLit(i) => Seq(Int)
      case PResultLit() =>
        curMember match {
          case PFunction(_, _, typ, _, _, _) =>
            Seq(typ)
          case _ => Nil
        }
      case PBoolLit(b) => Seq(Bool)
      case PNullLit() => Seq(Ref)
      case PLocationAccess(rcv, idnuse) =>
        names.definition(curMember)(idnuse) match {
          case PField(_, typ) =>
            Seq(typ)
          case _ => Nil
        }
      case PFunctApp(func, args) => ???
      case PUnfolding(loc, e) => Seq(Bool)
      case PExists(variable, e) => Seq(Bool)
      case PForall(variable, e) => Seq(Bool)
      case PCondExp(cond, thn, els) => possibleTypes(thn) intersect possibleTypes(els)
      case PCurPerm(loc) => Seq(Perm)
      case PNoPerm() => Seq(Perm)
      case PFullPerm() => Seq(Perm)
      case PWildcard() => Seq(Perm)
      case PConcretePerm(a, b) => Seq(Perm)
      case PEpsilon() => Seq(Perm)
      case PAccPred(loc, perm) => Seq(Bool)
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

  def definition(member: PMember)(idnuse: PIdnUse) = {
    if (member == null) {
      idnMap.get(idnuse.name).get.asInstanceOf[RealEntity]
    }
    else {
      // lookup in method map first, and otherwise in the general one
      memberIdnMap.get(member).get.getOrElse(idnuse.name,
        idnMap.get(idnuse.name).get
      ).asInstanceOf[RealEntity]
    }
  }

  private val idnMap = collection.mutable.HashMap[String, Entity]()
  private val memberIdnMap = collection.mutable.HashMap[PMember, collection.mutable.HashMap[String, Entity]]()

  def run(p: PProgram): Boolean = {
    var curMember: PMember = null
    def getMap = if (curMember == null) idnMap else memberIdnMap.get(curMember).get
    // find all declarations
    p.visit({
      case m: PMember =>
        memberIdnMap.put(m, collection.mutable.HashMap[String, Entity]())
        curMember = m
      case i@PIdnDef(name) =>
        getMap.get(name) match {
          case Some(MultipleEntity()) =>
            message(i, s"$name already defined.")
          case Some(e) =>
            message(i, s"$name already defined.")
            getMap.put(name, MultipleEntity())
          case None =>
            i.parent match {
              case decl: PProgram => idnMap.put(name, decl)
              case decl: PMethod => idnMap.put(name, decl)
              case decl: PLocalVarDecl => getMap.put(name, decl)
              case decl: PFormalArgDecl => getMap.put(name, decl)
              case decl: PField => idnMap.put(name, decl)
              case decl: PFunction => idnMap.put(name, decl)
              case decl: PPredicate => idnMap.put(name, decl)
              case decl: PDomain => idnMap.put(name, decl)
              case _ => sys.error(s"unexpected parent of identifier: ${i.parent}")
            }
        }
      case _ =>
    }, {
      case _: PMember =>
        curMember = null
      case _ =>
    })
    // check all identifier uses
    p.visit({
      case m: PMember =>
        curMember = m
      case i@PIdnUse(name) =>
        // look up in both maps (if we are not in a method currently, we look in the same map twice, but that is ok)
        getMap.getOrElse(name, idnMap.getOrElse(name, UnknownEntity())) match {
          case UnknownEntity() =>
            message(i, s"$name not defined.")
          case _ =>
        }
      case _ =>
    }, {
      case m: PMember =>
        curMember = null
      case _ =>
    })
    messagecount == 0
  }
}
