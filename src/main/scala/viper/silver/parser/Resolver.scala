/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import scala.collection.mutable
import scala.reflect._
import org.kiama.util.Messaging

/**
 * A resolver and type-checker for the intermediate SIL AST.
 */
case class Resolver(p: PProgram) {
  val names = NameAnalyser()
  val typechecker = TypeChecker(names)

  def run: Option[PProgram] = {
    if (names.run(p))
      if (typechecker.run(p))
        return Some(p)

    None
  }

  def messages = names.messages ++ typechecker.messages // ++ Consistency.messages // shouldn't be needed - Consistency errors should be generated only in later phases.
}

/**
 * Performs type-checking and sets the type of all typed nodes.
 */
case class TypeChecker(names: NameAnalyser) {

  import TypeHelper._

  var curMember: PScope = null
  var curFunction: PFunction = null
  var resultAllowed : Boolean = false

  /** to record error messages */
  var messages : Messaging.Messages = Nil

  def run(p: PProgram): Boolean = {
    check(p)
    messages.size == 0
  }

  def check(p: PProgram) {
    p.domains map check
    p.fields map check
    p.functions map check
    p.predicates map check
    p.methods map check

    /* Report any domain type that couldn't be resolved */
    p visit {
      case dt: PDomainType if dt.isUndeclared => messages ++= Messaging.message(dt, s"found undeclared type ${dt.domain.name}")
    }
  }

  def checkMember(m: PScope)(fcheck: => Unit) {
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
      assert(curFunction==null)
      curFunction=f
      check(f.typ)
      f.formalArgs map (a => check(a.typ))
      check(f.typ)
      f.pres map (check(_, Bool))
      resultAllowed=true
      f.posts map (check(_, Bool))
      f.body.map(check(_, f.typ)) //result in the function body gets the error message somewhere else
      resultAllowed=false
      curFunction=null
    }
  }


  def check(p: PPredicate) {
    checkMember(p) {
      p.formalArgs map (a => check(a.typ))
      p.body.map(check(_, Bool))
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
    checkMember(a) {
      check(a.exp, Bool)
    }
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
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be folded")
        check(e, Bool)
      case PUnfold(e) =>
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be unfolded")
        check(e, Bool)
      case PExhale(e) =>
        check(e, Bool)
      case PAssert(e) =>
        check(e, Bool)
      case PInhale(e) =>
        check(e, Bool)
      case PVarAssign(idnuse, PFunctApp(func, args)) if names.definition(curMember)(func).isInstanceOf[PMethod] =>
        /* This is a method call that got parsed in a slightly confusing way.
         * TODO: Get rid of this case! There is a matching case in the translator.
         */
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
            messages ++= Messaging.message(stmt, "expected variable as lhs")
        }
      case PNewStmt(target, fields) =>
        val msg = "expected variable as lhs"
        acceptAndCheckTypedEntity[PLocalVarDecl, PFormalArgDecl](Seq(target), msg){(v, _) => check(v, Ref)}
        fields map (_.map (field =>
          names.definition(curMember)(field, Some(PField.getClass)) match {
            case PField(_, typ) =>
              check(field, typ)
            case _ =>
              messages ++= Messaging.message(stmt, "expected a field as lhs")
          }))
      case PMethodCall(targets, method, args) =>
        names.definition(curMember)(method) match {
          case PMethod(_, formalArgs, formalTargets, _, _, _) =>
            if (formalArgs.length != args.length) {
              messages ++= Messaging.message(stmt, "wrong number of arguments")
            } else {
              if (formalTargets.length != targets.length) {
                messages ++= Messaging.message(stmt, "wrong number of targets")
              } else {
                for ((formal, actual) <- (formalArgs zip args) ++ (formalTargets zip targets)) {
                  check(actual, formal.typ)
                }
              }
            }
          case _ =>
            messages ++= Messaging.message(stmt, "expected a method")
        }
      case PLabel(name) =>
      // nothing to check
      case PGoto(label) =>
        names.definition(curMember)(label) match {
          case PLabel(_) =>
          case _ =>
            messages ++= Messaging.message(stmt, "expected a label")
        }
      case PFieldAssign(field, rhs) =>
        names.definition(curMember)(field.idnuse, Some(PField.getClass)) match {
          case PField(_, typ) =>
            check(field, typ)
            check(rhs, typ)
          case _ =>
            messages ++= Messaging.message(stmt, "expected a field as lhs")
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
        check(typ)
        init match {
          case Some(i) => check(i, typ)
          case None =>
        }
      case PFresh(vars) =>
        val msg = "expected variable in fresh read permission block"
        acceptAndCheckTypedEntity[PLocalVarDecl, PFormalArgDecl](vars, msg){(v, _) => check(v, Perm)}
      case PConstraining(vars, s) =>
        val msg = "expected variable in fresh read permission block"
        acceptAndCheckTypedEntity[PLocalVarDecl, PFormalArgDecl](vars, msg){(v, _) => check(v, Perm)}
        check(s)
      case _: PDefine =>
        /* Should have been removed right after parsing */
        sys.error(s"Unexpected node $stmt found")
      case _: PSkip =>
    }
  }

  def acceptNonAbstractPredicateAccess(exp: PExp, messageIfAbstractPredicate: String) {
    exp match {
      case PAccPred(PPredicateAccess(_, idnuse), _) =>
        acceptAndCheckTypedEntity[PPredicate, Nothing](Seq(idnuse), "expected predicate"){(_, _predicate) =>
          val predicate = _predicate.asInstanceOf[PPredicate]
          if (predicate.body.isEmpty) messages ++= Messaging.message(idnuse, messageIfAbstractPredicate)
        }
      case _ => messages ++= Messaging.message(exp, "expected predicate access")
    }
  }

  /** This handy method checks if all passed `idnUses` refer to specific
    * subtypes `TypedEntity`s when looked up in the current scope/lookup table.
    * For each element in `idnUses`, if it refers an appropriate subtype, then
    * `handle` is applied to the current element of `idnUses` and to the
    * `TypedEntity` it refers to.
    *
    * If only a single subtype of `TypedEntity` is acceptable, pass `Nothing`
    * as the second type argument.
    *
    * Caution is advised, however, since the method checks various
    * type-relations only at runtime.
    *
    * @param idnUses Identifier usages to check
    * @param errorMessage Error message in case one of the identifiers usages
    *                     does not refer to an appropriate subtype of
    *                     `TypedEntity`
    * @param handle Handle pairs of current identifier usage and referenced
    *               `TypedEntity`
    * @tparam T1 An accepted subtype of `TypedEntity`
    * @tparam T2 Another accepted subtype of `TypedEntity`
    *
    * TODO: Generalise the method to take ClassTags T1, ..., TN.
    * TODO: If only a single T is taken, let handle be (PIdnUse, T) => Unit
    */
  def acceptAndCheckTypedEntity[T1 : ClassTag, T2 : ClassTag]
                               (idnUses: Seq[PIdnUse], errorMessage: String)
                               (handle: (PIdnUse, PTypedDeclaration) => Unit = (_, _) => ()) {

    /* TODO: Ensure that the ClassTags denote subtypes of TypedEntity */
    val acceptedClasses = Seq[Class[_]](classTag[T1].runtimeClass, classTag[T2].runtimeClass)

    idnUses.foreach { use =>
      val decl = names.definition(curMember)(use)

      acceptedClasses.find(_.isInstance(decl)) match {
        case Some(_) =>
          handle(use, decl.asInstanceOf[PTypedDeclaration])
        case None =>
          messages ++= Messaging.message(use, errorMessage)
      }
    }
  }

  def check(typ: PType) {
    typ match {
      case _: PPredicateType =>
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
            dt.kind = PDomainTypeKinds.Domain
          case PTypeVarDecl(typeVar) =>
            dt.kind = PDomainTypeKinds.TypeVar
          case other =>
            dt.kind = PDomainTypeKinds.Undeclared
        }

      case PSeqType(elemType) =>
        check(elemType)
      case PSetType(elemType) =>
        check(elemType)
      case PMultisetType(elemType) =>
        check(elemType)
      case PUnknown() =>
        messages ++= Messaging.message(typ, "expected concrete type, but found unknown type")
    }
  }

  /**
   * Look at two valid types for an expression and attempts to learn the instantiations for
   * type variables.  Returns a mapping of type variables to types.
   */
  def learn(a: PType, b: PType): Seq[(String, PType)] = {
    @inline
    def multiLearn(as: Seq[PType], bs: Seq[PType]) =
      (0 until as.length) flatMap (i => learn(as(i), bs(i)))

    (a, b) match {
      case (PTypeVar(name), t) if t.isConcrete => Seq(name -> t)
      case (t, PTypeVar(name)) if t.isConcrete => Seq(name -> t)
      case (PSeqType(e1), PSeqType(e2)) =>
        learn(e1, e2)
      case (PSetType(e1), PSetType(e2)) =>
        learn(e1, e2)
      case (PMultisetType(e1), PMultisetType(e2)) =>
        learn(e1, e2)
      case (dt1 @ PDomainType(n1, m1), dt2 @ PDomainType(n2, m2)) if m1.length == m2.length =>
        if (n1 == n2)
          multiLearn(m1, m2)
        else if (dt1.isTypeVar && dt2.isConcrete)
          (dt1.domain.name -> dt2) +: multiLearn(m1, m2)
        else if (dt2.isTypeVar && dt1.isConcrete)
          (dt2.domain.name -> dt1) +: multiLearn(m1, m2)
        else
          Nil
      case _ => Nil
    }
  }

  /**
   * Are types 'a' and 'b' compatible?  Type variables are assumed to be unbound so far,
   * and if they occur they are compatible with any type. PUnknown is also compatible with
   * everything, as are undeclared PDomainTypes.
   */
  def isCompatible(a: PType, b: PType): Boolean = {
    (a, b) match {
      case _ if a == b => true
      case (PUnknown(), _) | (_, PUnknown()) => true
      case (dt: PDomainType, _) if dt.isUndeclared => true
      case (_, dt: PDomainType) if dt.isUndeclared => true
      case (PTypeVar(_), _) | (_, PTypeVar(_)) => true
      case (PSeqType(e1), PSeqType(e2)) => isCompatible(e1, e2)
      case (PSetType(e1), PSetType(e2)) => isCompatible(e1, e2)
      case (PMultisetType(e1), PMultisetType(e2)) => isCompatible(e1, e2)
      case (PDomainType(domain1, args1), PDomainType(domain2, args2))
        if domain1 == domain2 && args1.length == args2.length =>
        (args1 zip args2) forall (x => isCompatible(x._1, x._2))
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
    val expected = expectedRaw filter {
      case PTypeVar(_) => false
      case _ => true
    }
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
          messages ++= Messaging.message(exp, s"expected type $expectedString, but got $actual at the expression at ${exp.start}-${exp.finish}")
        }
      }
    }
    /**
     * Issue an error for the node at 'n'. Also sets an error type for 'exp' to suppress
     * further warnings.
     *
     * TODO: Similar to Consistency.recordIfNot. Combine!
     */
    def issueError(n: KiamaPositioned, m: String) {
      messages ++= Messaging.message(n, m)
      setErrorType() // suppress further warnings
    }

    /**
     * Sets an error type for 'exp' to suppress further warnings.
     */
    def setErrorType() {
      setType(PUnknown())
    }

    def genericSeqType: PSeqType = PSeqType(PTypeVar("."))
    def genericSetType: PSetType = PSetType(PTypeVar("."))
    def genericMultisetType: PMultisetType = PMultisetType(PTypeVar("."))
    def genericAnySetType = Seq(genericSetType, genericMultisetType)

    def setPIdnUseTypeAndEntity(piu: PIdnUse, typ: PType, entity: PDeclaration) {
      setType(typ)
      piu.decl = entity
    }

    exp match {
      case piu @ PIdnUse(name) =>
        names.definition(curMember)(piu) match {
          case decl @ PLocalVarDecl(_, typ, _) => setPIdnUseTypeAndEntity(piu, typ, decl)
          case decl @ PFormalArgDecl(_, typ) => setPIdnUseTypeAndEntity(piu, typ, decl)
          case decl @ PField(_, typ) => setPIdnUseTypeAndEntity(piu, typ, decl)
          case decl @ PPredicate(_, _, _) => setPIdnUseTypeAndEntity(piu, Pred, decl)
          case x => issueError(piu, s"expected identifier, but got $x")
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
                  setType(right.typ)
                }
            }
          case "/" =>
            check(left, Seq(Int,Perm))
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
            check(right, genericAnySetType ++ Seq(genericSeqType))
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
            } else if (!right.typ.isInstanceOf[PSeqType] &&
              !right.typ.isInstanceOf[PSetType] &&
              !right.typ.isInstanceOf[PMultisetType]) {
              issueError(right, s"expected set, multiset or sequence type, but found ${right.typ}")
            } else if (
              (right.typ.isInstanceOf[PSeqType] && !isCompatible(left.typ, right.typ.asInstanceOf[PSeqType].elementType)) ||
                (right.typ.isInstanceOf[PSetType] && !isCompatible(left.typ, right.typ.asInstanceOf[PSetType].elementType)) ||
                (right.typ.isInstanceOf[PMultisetType] && !isCompatible(left.typ, right.typ.asInstanceOf[PMultisetType].elementType))
                ) {
              issueError(right, s"element $left with type ${left.typ} cannot be in a sequence/set of type ${right.typ}")
            }
            // TODO: perform type refinement and propagate down
            if (right.typ.isInstanceOf[PMultisetType]) setType(Int) else setType(Bool)
          case "++" =>
            val newExpected = if (expected.isEmpty) Seq(genericSeqType) else expected
            check(left, newExpected)
            check(right, newExpected)
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
              setErrorType()
            } else if (!right.typ.isInstanceOf[PSeqType] || !left.typ.isInstanceOf[PSeqType]){
              setErrorType()
              issueError(exp, s"left- and right-hand-side of ++ must be sequences, but found ${left.typ} and ${right.typ}")
            }
            else if (isCompatible(left.typ, right.typ)) {
              // ok
              // TODO: perform type refinement and propagate down
              setType(left.typ)
            } else {
              issueError(exp, s"left- and right-hand-side must have same type, but found ${left.typ} and ${right.typ}")
            }
          case "union" | "intersection" | "setminus" =>
            val newExpected = if (expected.isEmpty) genericAnySetType else expected
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
          case "subset" =>
            val newExpected = genericAnySetType
            check(left, newExpected)
            check(right, newExpected)
            if (left.typ.isUnknown || right.typ.isUnknown) {
              // nothing to do, error has already been issued
              setErrorType()
            } else if (isCompatible(left.typ, right.typ)) {
              // ok
              // TODO: perform type refinement and propagate down
              setType(Bool)
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
        if (resultAllowed)
          setType(curFunction.typ)
        else
          issueError(r, "'result' can only be used in function postconditions")
      case PBoolLit(b) =>
        setType(Bool)
      case PNullLit() =>
        setType(Ref)
      case PFieldAccess(rcv, idnuse) =>
        /* For a field access of the type rcv.fld we have to ensure that the
         * receiver denotes a local variable. Just checking that it is of type
         * Ref is not sufficient, since it could also denote a Ref-typed field.
         */
        rcv match {
          case p: PIdnUse =>
            acceptAndCheckTypedEntity[PLocalVarDecl, PFormalArgDecl](Seq(p), "expected local variable")()
          case _ =>
            /* More complicated expressions should be ok if of type Ref, which is checked next */
        }
        check(rcv, Ref)
        acceptAndCheckTypedEntity[PField, Nothing](Seq(idnuse), "expected field")((_, _) => check(idnuse, expected))
        setType(idnuse.typ)
      case p@PPredicateAccess(args, idnuse) =>
        acceptAndCheckTypedEntity[PPredicate, Nothing](Seq(idnuse), "expected predicate"){(_, _predicate) =>
          val predicate = _predicate.asInstanceOf[PPredicate]
          check(idnuse, expected)
          /* Check that the predicate is used with 1. the correct number of arguments,
           * and 2. with the correct types of arguments.
           */
          if (args.length != predicate.formalArgs.length) issueError(idnuse, "predicate arity doesn't match")
          args zip predicate.formalArgs map {case (aarg, farg) => check(aarg, farg.typ)}
        }
        setType(Pred)
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
            val inferred = mutable.ListBuffer[(String, PType)]()
            (formalArgs zip args) foreach {
              case (formal, actual) =>
                check(actual, formal.typ)
                inferred ++= learn(actual.typ, formal.typ)
            }
            // also infer type information based on the context (expected type)
            if (expected.size == 1) {
              inferred ++= learn(typ, expected.head)
            }
            setRefinedType(typ, inferred)
          case x =>
            issueError(func, "expected function")
        }
      case PUnfolding(acc, body) =>
        check(acc.perm, Perm)
        check(acc.loc, Pred)
        acceptNonAbstractPredicateAccess(acc, "abstract predicates cannot be unfolded")
        check(body, expected)
        setType(exp.typ)
      case PLet(exp1, nestedScope @ PLetNestedScope(variable, body)) =>
        check(exp1, Nil)
        val oldCurMember = curMember
        curMember = nestedScope
        variable.typ = exp1.typ
        check(body, expected)
        setType(body.typ)
        curMember = oldCurMember
      case _: PLetNestedScope =>
        issueError(exp, "expected node")
      case f@ PExists(vars, e) =>
        val oldCurMember = curMember
        curMember = f
        vars map (v => check(v.typ))
        check(e, Bool)
        curMember = oldCurMember
      case f@ PForall(vars, triggers, e) =>
        val oldCurMember = curMember
        curMember = f
        vars map (v => check(v.typ))
        triggers.flatten map (x => check(x, Nil))
        check(e, Bool)
        curMember = oldCurMember
      case po: POldExp =>
        check(po.e, expected)
        if (po.e.typ.isUnknown) {
          setErrorType()
        } else {
//          if (!isPure(po.e.is))
            //issueError(po, "old expressions must be pure")
//          else
            // ok
            setType(po.e.typ)
        }

      case f@ PForallReferences(v,fields, e) =>
        val oldCurMember = curMember
        curMember = f
        check(f.variable.typ)
        if(! isCompatible(f.variable.typ,Ref)){
          val t = f.variable
          messages ++= Messaging.message(v, s"expected $Ref, but got $t")
        }
        check(e, Bool)
        curMember = oldCurMember

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
      case PInhaleExhaleExp(in, ex) =>
        check(in, Bool)
        check(ex, Bool)
        setType(Bool)
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
      case PEmptySeq(_) =>
        val typ = if (exp.typ.isUnknown) genericSeqType else exp.typ
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
          case _ => expected map PSeqType
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
      case PSize(seq) =>
        if (expected.nonEmpty && !(expected contains Int)) {
          issueError(exp, s"expected $expectedString, but found |.| which has type Int")
        } else {
          check(seq, Seq(genericSeqType, genericSetType, genericMultisetType))
          setType(Int)
        }
      case PEmptySet(t) =>
//        val typ = genericSetType
/*        if (expected.size == 1) {
          setRefinedType(typ, learn(typ, expected.head))
        } else {
          setType(typ)
    }                 */ //inference
        setType(PSetType(t))
      case PExplicitSet(elems) =>
        assert(elems.nonEmpty)
        val expectedElemTyp = (expected map {
          case PSetType(e) => Some(e)
          case _ => None
        }) filter (_.isDefined) map (_.get)
        elems map (check(_, expectedElemTyp))
        elems map (_.typ) filterNot (_.isUnknown) match {
          case Nil =>
            // all elements have an error type
            setErrorType()
          case types =>
            for (t <- types.tail) {
              ensure(isCompatible(t, types.head), exp,
                s"expected the same type for all elements of the explicit set, but found ${types.head} and $t")
            }
            // TODO: perform type inference and propagate type down
            setType(PSetType(types.head))
        }
      case PEmptyMultiset(t) =>
/*        val typ = genericMultisetType
        if (expected.size == 1) {
          setRefinedType(typ, learn(typ, expected.head))
        } else {
          setType(typ)
        }*/
        setType(PMultisetType(t))
      case PExplicitMultiset(elems) =>
        assert(elems.nonEmpty)
        val expectedElemTyp = (expected map {
          case PMultisetType(e) => Some(e)
          case _ => None
        }) filter (_.isDefined) map (_.get)
        elems map (check(_, expectedElemTyp))
        elems map (_.typ) filterNot (_.isUnknown) match {
          case Nil =>
            // all elements have an error type
            setErrorType()
          case types =>
            for (t <- types.tail) {
              ensure(isCompatible(t, types.head), exp,
                s"expected the same type for all elements of the explicit multiset, but found ${types.head} and $t")
            }
            // TODO: perform type inference and propagate type down
            setType(PMultisetType(types.head))
        }
    }
  }

  /**
   * If b is false, report an error for node.
   */
  def ensure(b: Boolean, node: KiamaPositioned, msg: String) {
    if (!b) messages ++= Messaging.message(node, msg)
  }
}

/**
 * Resolves identifiers to their declaration.
 */
case class NameAnalyser() {

  /** To record error messages */
  var messages : Messaging.Messages = Nil


  /** Resolves the entity to which the given identifier `idnuse` refers.
    *
    * If `member` is not null then the identifier will first be looked up in
    * the scope defined by the member. If it fails (or if the member is null),
    * the wider scope will be considered.
    *
    * In order to resolve name clashes, e.g., if the identifier is expected to
    * refer to a field, but there is a local variable with the same name in the
    * member scope that shadows the field, then the `expected` class can be
    * provided (e.g., `PField`), with the result that the shadowing local
    * variable will be ignored because its class (`PLocalVarDecl`) doesn't
    * match.
    *
    * @param member Current scope in which to start the resolving.
    * @param idnuse Identifier that is to be resolved.
    * @param expected Expected class of the entity.
    * @return Resolved entity.
    */
  def definition(member: PScope)(idnuse: PIdnUse, expected: Option[Class[_]] = None): PDeclaration = {
    if (member == null) {
      globalDeclarationMap.get(idnuse.name).get.asInstanceOf[PDeclaration]
    } else {
      // lookup in method map first, and otherwise in the general one
      val entity =
        localDeclarationMaps.get(member.scopeId).get.get(idnuse.name) match {
          case None =>
            globalDeclarationMap.get(idnuse.name).get
          case Some(foundEntity) =>
            if (expected.isDefined && foundEntity.getClass != expected.get)
              globalDeclarationMap.get(idnuse.name).get
            else
              foundEntity
        }

      entity.asInstanceOf[PDeclaration] // TODO: Why is the cast necessary? Remove if possible.
    }
  }

  def reset() {
    globalDeclarationMap.clear()
    localDeclarationMaps.clear()
  }

  private val globalDeclarationMap = mutable.HashMap[String, PEntity]()

  /* [2014-11-13 Malte] Changed localDeclarationMaps to be a map from PScope.Id
   * instead of from PScope directly. This was necessary in order to support
   * changing PScopes during type-checking, e.g., when changing the type of a
   * variable bound by a let-expression. This change (potentially) affects the
   * hashcode of the let-expression (which is a PScope), which in turn affects
   * localDeclarationMaps because such that the value stored for scope cannot
   * be retrieved anymore.
   */
  private val localDeclarationMaps = mutable.HashMap[PScope.Id, mutable.HashMap[String, PEntity]]()

  def run(p: PProgram): Boolean = {
    var curMember: PScope = null
    def getMap(d:PNode) : mutable.HashMap[String, PEntity] =
      d match {
        case d: PGlobalDeclaration => globalDeclarationMap
        case _ => getCurrentMap
      }
    def getCurrentMap: mutable.HashMap[String, PEntity] =
      if (curMember == null) globalDeclarationMap else localDeclarationMaps.get(curMember.scopeId).get

    val scopeStack = mutable.Stack[PScope]()

    val nodeDownNameCollectorVisitor = new PartialFunction[PNode,Unit] {
      def apply(n:PNode) = {
        n match {
          case d: PDeclaration =>
            getMap(d).get(d.idndef.name) match {
              case Some(e: PDeclaration) =>
                messages ++= Messaging.message(e, "Duplicate identifier \"" + e.idndef.name + "\" : at " + e.idndef.start + " and at " + d.idndef.start)
              case Some(e:PErrorEntity) =>
              case None =>
                globalDeclarationMap.get(d.idndef.name) match {
                  case Some(e: PDeclaration) =>
                    messages ++= Messaging.message(e, "Identifier shadowing \"" + e.idndef.name + "\" : at " + e.idndef.start + " and at " + d.idndef.start)
                  case Some(e:PErrorEntity) =>
                  case None =>
                    getMap(d).put(d.idndef.name, d)
                }
              }
          case _ =>
        }

        n match {
          case s: PScope =>
            val localDeclarations =
              if (curMember == null)
                mutable.HashMap[String, PEntity]()
              else
                localDeclarationMaps.getOrElse(curMember.scopeId, mutable.HashMap[String, PEntity]()).clone()

            localDeclarationMaps.put(s.scopeId, localDeclarations)
            scopeStack.push(curMember)
            curMember = s
          case _ =>
        }
      }

      def isDefinedAt(n:PNode) = {
        n match {
          case d: PDeclaration => true
          case s: PScope => true
          case _ => false
        }
      }
    }

    val nodeUpNameCollectorVisitor = new PartialFunction[PNode,Unit] {
      def apply(n:PNode) = {
        n match {
          case _: PScope =>
            curMember = scopeStack.pop()
          case _ =>
        }
      }
      def isDefinedAt(n:PNode) = {
        n match {
          case s: PScope => true
          case _ => false
        }
      }
    }

    // find all declarations
    p.visit( nodeDownNameCollectorVisitor,nodeUpNameCollectorVisitor)

    /* Check all identifier uses. */
    p.visit({
      case m: PScope =>
        scopeStack.push(curMember)
        curMember = m
      case i@PIdnUse(name) =>
        // look up in both maps (if we are not in a method currently, we look in the same map twice, but that is ok)
        getCurrentMap.getOrElse(name, globalDeclarationMap.getOrElse(name, PUnknownEntity())) match {
          case PUnknownEntity() =>
            // domain types can also be type variables, which need not be declared
            if (!i.parent.isInstanceOf[PDomainType]) {
              messages ++= Messaging.message(i, s"identifier $name not defined.")
            }
          case _ =>
        }
      case _ =>
    }, {
      case m: PScope =>
        curMember = scopeStack.pop()
      case _ =>
    })

    messages.isEmpty
  }
}
