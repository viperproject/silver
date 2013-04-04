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
      case dt@PDomainType(domain, args) =>
        args map check
        var x: Any = null
        try {
          x = names.definition(curMember)(domain)
        } catch {
          case _: Throwable =>
        }
        x match {
          case d@PDomain(name, typVars, _, _) =>
            ensure(args.length == typVars.length, typ, "wrong number of type arguments")
            dt._isTypeVar = Some(false)
          case _ =>
            if (args.length == 0) {
              // this must be a type variable, then
              dt._isTypeVar = Some(true)
            } else {
              message(typ, "expected domain")
            }
        }
      case PSeqType(elemType) =>
        check(elemType)
      case PUnkown() =>
        message(typ, "expected concrete type, but found unknown typ")
    }
  }

  /**
   * Look at two valid types for an expression and attempts to learn the instantiations for
   * type variables.  Returns a mapping of type variables to types.
   */
  def learn(a: PType, b: PType): Seq[(String, PType)] = {
    (a, b) match {
      case (PTypeVar(name), t) if t.isConcrete => Seq(name -> t)
      case (t, PTypeVar(name)) if t.isConcrete => Seq(name -> t)
      case (PDomainType(n1, m1), PDomainType(n2, m2))
        if n1 == n2 && m1.length == m2.length =>
        (m1 zip m2) flatMap (x => learn(x._1, x._2))
      case _ => Nil
    }
  }

  /**
   * Are types 'a' and 'b' compatible?  Type variables are assumed to be unbound so far,
   * and if they occur they are compatible with any type.  PUnkown is also compatible with
   * everything.
   */
  def isCompatible(a: PType, b: PType): Boolean = {
    (a, b) match {
      case (PUnkown(), t) => true
      case (t, PUnkown()) => true
      case (PTypeVar(name), t) => true
      case (t, PTypeVar(name)) => true
      case (PSeqType(e1), PSeqType(e2)) => isCompatible(e1, e2)
      case _ if a == b => true
      case _ => false
    }
  }

  /**
   * Type-check and resolve e and ensure that it has type expected.  If that is not the case, then an
   * error should be issued.
   *
   * The empty set can be passed for expected, if any type is fine.
   */
  def check(exp: PExp, expected: PType): Unit = check(exp, Seq(expected))
  def check(exp: PExp, expected: Seq[PType]): Unit = {
    def setType(actual: PType) {
      if (actual.isUnknown) {
        // no error for unknown type (an error has already been issued)
        exp.typ = actual
      } else {
        var found = false
        if (expected.isEmpty) {
          found = true
          exp.typ = actual
        }
        for (e <- expected) {
          if (!found && isCompatible(e, actual)) {
            found = true
            exp.typ = actual
          }
        }
        if (!found) {
          if (expected.size == 1) {
            message(exp, s"expected ${expected.head}, but got $actual")
          } else {
            message(exp, s"expected one of $expected, but got $actual")
          }
        }
      }
    }
    def issueError(n: Positioned, m: String) {
      message(n, m)
      setType(PUnkown()) // suppress further warnings
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
            issueError(i, s"expected variable or field, but got $x")
        }
      case PBinExp(left, op, right) =>
        op match {
          case "+" | "-" =>
            expected.filter(x => Seq(Int, Perm) contains x) match {
              case Nil =>
                issueError(exp, s"expected type $expected, but found operator $op that cannot have such a type")
              case expectedStillPossible =>
                check(left, expectedStillPossible)
                check(right, expectedStillPossible)
                if (left.typ.isUnknown || right.typ.isUnknown) {
                  setType(PUnkown()) // error has already been issued
                } else if (left.typ == right.typ) {
                  setType(left.typ)
                } else {
                  issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
                }
            }
          case "*" => ???
          case "/" => ???
          case "%" => ???
          case "<" | "<=" | ">" | ">=" =>
            check(left, Seq(Int, Perm))
            check(right, Seq(Int, Perm))
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
            } else if (left.typ == right.typ) {
              // ok
            } else {
              issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
            }
            setType(Bool)
          case "==" | "!=" =>
            check(left, Nil) // any type is fine
            check(right, Nil)
            if (left.typ == right.typ) {
              // ok
            } else {
              issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
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
            expected.filter(x => Seq(Int, Perm) contains x) match {
              case Nil =>
                issueError(exp, s"expected type $expected, but found unary operator $op that cannot have such a type")
              case expectedStillPossible =>
                check(e, expectedStillPossible)
                if (e.typ.isUnknown) {
                  // nothing to do, error has already been issued
                } else {
                  // ok
                  setType(e.typ)
                }
            }
          case "!" =>
            check(e, Bool)
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
            issueError(r, "'result' can only be used in functions")
        }
      case PBoolLit(b) =>
        setType(Bool)
      case PNullLit() =>
        setType(Ref)
      case PLocationAccess(rcv, idnuse) =>
        check(rcv, Ref)
        check(idnuse, expected)
        setType(idnuse.typ)
      case fa@PFunctApp(func, args) =>
        names.definition(curMember)(func) match {
          case PFunction(_, formalArgs, typ, _, _, _) =>
            ensure(formalArgs.size == args.size, fa, "wrong number of arguments")
            (formalArgs zip args) foreach {
              case (formal, actual) =>
                check(actual, formal.typ)
            }
            setType(typ)
          case PDomainFunction(_, formalArgs, typ) =>
            ensure(formalArgs.size == args.size, fa, "wrong number of arguments")
            val inferred = collection.mutable.ListBuffer[(String, PType)]()
            (formalArgs zip args) foreach {
              case (formal, actual) =>
                check(actual, formal.typ)
                // infer type information based on arguments
                inferred ++= learn(actual.typ, formal.typ)
            }
            // also infer type information based on the context (expected type)
            if (expected.size == 1) {
              inferred ++= learn(typ, expected.head)
            }
            setType(typ.substitute(inferred.toMap))
          case x =>
            issueError(func, s"expected function")
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
        check(loc, Seq())
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
        check(loc, Seq())
        check(perm, Perm)
      case PEmptySeq() => ???
      case PExplicitSeq(elems) => ???
      case PRangeSeq(low, high) => ???
      case PSeqElement(seq, idx) => ???
      case PSeqTake(seq, n) => ???
      case PSeqDrop(seq, n) => ???
      case PSeqUpdate(seq, idx, elem) => ???
      case PPSeqLength(seq) => ???
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
              case decl: PDomainFunction => idnMap.put(name, decl)
              case decl: PAxiom => // nothing refors to axioms, thus do not store it
              case decl: PPredicate => idnMap.put(name, decl)
              case decl: PDomain =>
                if (name == decl.idndef.name)
                  idnMap.put(name, decl)
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
            // domain types can also be type variables, which need not be declared
            if (!i.parent.isInstanceOf[PDomainType])
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
