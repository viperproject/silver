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
    // first, check all types to make sure we know what PDomainType's are actually
    // domain types, and which are type variables.
    p visit {
      case t: PType =>
        check(t)
    }
    // now check all program parts
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
      case PVarAssign(idnuse, PFunctApp(func, args)) if names.definition(curMember)(func).isInstanceOf[PMethod] =>
        // this is a method call that got parsed in a slightly confusing way
        check(PMethodCall(Seq(idnuse), func, args))
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
      case PMethodCall(targets, method, args) =>
        names.definition(curMember)(method) match {
          case PMethod(_, formalArgs, formalTargets, _, _, _) =>
            if (formalArgs.length != args.length) {
              message(stmt, "wrong number of arguments")
            } else {
              if (formalTargets.length != targets.length) {
                message(stmt, "wrong number of targets")
              } else {
                for ((formal, actual) <- (formalArgs zip args) ++ (formalTargets zip targets)) {
                  check(actual, formal.typ)
                }
              }
            }
          case _ =>
            message(stmt, "expected a label")
        }
      case PLabel(name) =>
      // nothing to check
      case PGoto(label) =>
        names.definition(curMember)(label) match {
          case PLabel(_) =>
          case _ =>
            message(stmt, "expected a label")
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
        check(s)
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
      case (PSeqType(e1), PSeqType(e2)) =>
        learn(e1, e2)
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
      case (PDomainType(domain1, args1), PDomainType(domain2, args2))
        if domain1 == domain2 && args1.length == args2.length =>
        (args1 zip args2) forall (x => isCompatible(x._1, x._2))
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
  def check(exp: PExp, expectedRaw: Seq[PType]): Unit = {
    val expected = expectedRaw filter ({
      case PTypeVar(_) => false
      case _ => true
    })
    def setRefinedType(actual: PType, inferred: Seq[(String, PType)]) {
      val t = actual.substitute(inferred.toMap)
      check(t)
      setType(t)
    }
    /**
     * Turn 'expected' into a readable string.
     */
    lazy val expectedString = {
      if (expected.size == 1) {
        expected.head.toString
      } else {
        s"one of [${expected.mkString(", ")}]"
      }
    }
    /**
     * Set the type of 'exp', and check that the actual type is allowed by one of the expected types.
     */
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
          message(exp, s"expected $expectedString, but got $actual")
        }
      }
    }
    /**
     * Issue an error for the node at 'n'. Also sets an error type for 'exp' to suppress
     * further warnings.
     */
    def issueError(n: Positioned, m: String) {
      message(n, m)
      setErrorType() // suppress further warnings
    }
    /**
     * Sets an error type for 'exp' to suppress further warnings.
     */
    def setErrorType() {
      setType(PUnkown())
    }
    def genericSeqType: PSeqType = PSeqType(PTypeVar("."))
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
            val safeExpected = if (expected.size == 0) Seq(Int, Perm) else expected
            safeExpected.filter(x => Seq(Int, Perm) contains x) match {
              case Nil =>
                issueError(exp, s"expected $expectedString, but found operator $op that cannot have such a type")
              case expectedStillPossible =>
                check(left, expectedStillPossible)
                check(right, expectedStillPossible)
                if (left.typ.isUnknown || right.typ.isUnknown) {
                  setErrorType()
                } else if (left.typ == right.typ) {
                  setType(left.typ)
                } else {
                  issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
                }
            }
          case "*" =>
            val safeExpected = if (expected.size == 0) Seq(Int, Perm) else expected
            safeExpected.filter(x => Seq(Int, Perm) contains x) match {
              case Nil =>
                issueError(exp, s"expected $expectedString, but found operator $op that cannot have such a type")
              case expectedStillPossible =>
                expectedStillPossible match {
                  case Seq(Perm) =>
                    check(left, Seq(Perm, Int))
                    check(right, Perm)
                  case _ =>
                    check(left, expectedStillPossible)
                    check(right, expectedStillPossible)
                }
                if (left.typ.isUnknown || right.typ.isUnknown) {
                  setErrorType()
                } else {
                  setType(left.typ)
                }
            }
          case "/" =>
            check(left, Int)
            check(right, Int)
            setType(Perm)
          case "\\" =>
            check(left, Int)
            check(right, Int)
            setType(Int)
          case "%" =>
            check(left, Int)
            check(right, Int)
            setType(Int)
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
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
            } else if (isCompatible(left.typ, right.typ)) {
              // ok
              // TODO: perform type refinement and propagate down
            } else {
              issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
            }
            setType(Bool)
          case "&&" | "||" | "<==>" | "==>" =>
            check(left, Bool)
            check(right, Bool)
            setType(Bool)
          case "in" =>
            check(left, Nil)
            check(right, genericSeqType)
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
            } else if (!right.typ.isInstanceOf[PSeqType]) {
              issueError(right, s"expected sequence type, but found ${right.typ}")
            } else if (!isCompatible(left.typ, right.typ.asInstanceOf[PSeqType].elementType)) {
              issueError(right, s"element $left with type ${left.typ} cannot be in a sequence of type ${right.typ}")
            }
            // TODO: perform type refinement and propagate down
            setType(Bool)
          case "++" =>
            val newExpected = if (expected.isEmpty) Seq(genericSeqType) else expected
            check(left, newExpected)
            check(right, newExpected)
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
              setErrorType()
            } else if (isCompatible(left.typ, right.typ)) {
              // ok
              // TODO: perform type refinement and propagate down
              setType(left.typ)
            } else {
              issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
            }
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, e) =>
        op match {
          case "-" | "+" =>
            val safeExpected = if (expected.size == 0) Seq(Int, Perm) else expected
            safeExpected.filter(x => Seq(Int, Perm) contains x) match {
              case Nil =>
                issueError(exp, s"expected $expectedString, but found unary operator $op that cannot have such a type")
              case expectedStillPossible =>
                check(e, expectedStillPossible)
                if (e.typ.isUnknown) {
                  setErrorType()
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
          case PDomainFunction(_, formalArgs, typ, unique) =>
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
            setRefinedType(typ, inferred)
          case x =>
            issueError(func, s"expected function")
        }
      case PUnfolding(loc, e) =>
        check(loc, Pred)
        check(e, expected)
        setType(e.typ)
      case PExists(variable, e) =>
        check(variable.typ)
        check(e, Bool)
      case POld(e) =>
        check(e, expected)
        if (e.typ.isUnknown) {
          setErrorType()
        } else {
          // ok
          setType(e.typ)
        }
      case PForall(variable, triggers, e) =>
        triggers.flatten map (x => check(x, Nil))
        check(variable.typ)
        check(e, Bool)
      case PCondExp(cond, thn, els) =>
        check(cond, Bool)
        check(thn, Nil)
        check(els, Nil)
        if (thn.typ.isUnknown || els.typ.isUnknown) {
          setErrorType()
        } else if (isCompatible(thn.typ, els.typ)) {
          // ok
          // TODO: perform type refinement and propagate down
          setType(thn.typ)
        } else {
          issueError(exp, s"both branches of a conditional expression must have same type, but found ${thn.typ} and ${els.typ}")
        }
      case PCurPerm(loc) =>
        check(loc, Seq())
        setType(Perm)
      case PNoPerm() =>
        setType(Perm)
      case PFullPerm() =>
        setType(Perm)
      case PWildcard() =>
        setType(Perm)
      case PEpsilon() =>
        setType(Perm)
      case PAccPred(loc, perm) =>
        check(loc, Seq())
        check(perm, Perm)
        setType(Bool)
      case PEmptySeq() =>
        val typ = genericSeqType
        if (expected.size == 1) {
          setRefinedType(typ, learn(typ, expected.head))
        } else {
          setType(typ)
        }
      case PExplicitSeq(elems) =>
        assert(elems.nonEmpty)
        val expextedElemTyp = (expected map {
          case PSeqType(e) => Some(e)
          case _ => None
        }) filter (_.isDefined) map (_.get)
        elems map (check(_, expextedElemTyp))
        elems map (_.typ) filterNot (_.isUnknown) match {
          case Nil =>
            // all elements have an error type
            setErrorType()
          case types =>
            for (t <- types.tail) {
              ensure(isCompatible(t, types.head), exp,
                s"expected the same type for all elements of the explicit sequence, but found ${types.head} and $t")
            }
            // TODO: perform type inference and propagate type down
            setType(PSeqType(types.head))
        }
      case PRangeSeq(low, high) =>
        check(low, Int)
        check(high, Int)
        setType(PSeqType(Int))
      case PSeqIndex(seq, idx) =>
        val expectedSeqType = expected match {
          case Nil => Seq(genericSeqType)
          case _ => expected map (PSeqType(_))
        }
        check(seq, expectedSeqType)
        check(idx, Int)
        seq.typ match {
          case PSeqType(elemType) =>
            setType(elemType)
          case _ =>
            setErrorType()
        }
      case PSeqTake(seq, n) =>
        val expectedSeqType = expected match {
          case Nil => Seq(genericSeqType)
          case _ => expected
        }
        check(seq, expectedSeqType)
        check(n, Int)
        seq.typ match {
          case t: PSeqType =>
            setType(t)
          case _ =>
            setErrorType()
        }
      case PSeqDrop(seq, n) =>
        val expectedSeqType = expected match {
          case Nil => Seq(genericSeqType)
          case _ => expected
        }
        check(seq, expectedSeqType)
        check(n, Int)
        seq.typ match {
          case t: PSeqType =>
            setType(t)
          case _ =>
            setErrorType()
        }
      case PSeqUpdate(seq, idx, elem) =>
        val expectedSeqType = expected match {
          case Nil => Seq(genericSeqType)
          case _ => expected collect {
            case t: PSeqType => t
          }
        }
        if (expectedSeqType.isEmpty) {
          issueError(exp, s"expected $expected, but found a sequence update which has a sequence type")
        } else {
          check(seq, expectedSeqType)
          check(elem, expectedSeqType map (_.elementType))
          check(idx, Int)
          seq.typ match {
            case t: PSeqType =>
              if (!isCompatible(t.elementType, elem.typ)) {
                issueError(elem, s"found ${elem.typ} for $elem, but expected ${t.elementType}")
              } else {
                setType(t)
              }
            case _ =>
              setErrorType()
          }
        }
      case PSeqLength(seq) =>
        if (expected.nonEmpty && !(expected contains Int)) {
          issueError(exp, s"expected $expectedString, but found |.| which has type Int")
        } else {
          check(seq, genericSeqType)
          setType(Int)
        }
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
              case decl: PLabel =>
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
