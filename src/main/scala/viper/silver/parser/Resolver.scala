// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.FastMessaging
import viper.silver.ast.LabelledOld

import scala.collection.mutable
import scala.reflect._

/**
  * A resolver and type-checker for the intermediate Viper AST.
  */
case class Resolver(p: PProgram) {
  val names = NameAnalyser()
  val typechecker = TypeChecker(names)

  def run: Option[PProgram] = {
    val nameSuccess = names.run(p)
    // Run typechecker even if name resolution failed, to add more information to the
    // program, and report any other errors. A name resolution error should not cause
    // a typechecker error however!
    val typeckSuccess = try {
      typechecker.run(p)
    } catch {
      case e: Throwable =>
        // TODO: remove this try/catch once all assumptions that
        // name resolution succeeded are removed from the type checker
        val frame = e.getStackTrace().find(!_.getClassName().startsWith("scala")).map(_.toString()).getOrElse("")
        val msg = s"internal error during typechecking. Please file a bug report at https://github.com/viperproject/silver. Error \"${e.toString()}\" at \"$frame\""
        typechecker.messages ++= FastMessaging.message(p, msg)
        e.printStackTrace()
        false
    }
    if (nameSuccess && typeckSuccess)
      Some(p)
    else
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
  var resultAllowed: Boolean = false

  /** to record error messages */
  var messages: FastMessaging.Messages = Nil
  def success: Boolean = messages.isEmpty || messages.forall(m => !m.error)

  def run(p: PProgram): Boolean = {
    check(p)
    success
  }

  def check(p: PProgram): Unit = {

    /* [2022-03-14 Alessandro] Domain function declarations, method declarations and ordinary function declarations
     * must be checked before their application is checked. Especially, this is because type variables in signatures
     * must be resolved. However, the checks in the following block are independent of each other.
     */
    p.domains foreach checkFunctions
    p.fields foreach check
    p.functions foreach checkDeclaration
    p.predicates foreach checkDeclaration
    p.methods foreach checkDeclaration

    /* [2022-03-14 Alessandro] Unfortunately, there is currently no mechanism of checking some extensions "signature" first
     * and checking its "body" in a later step. However, there are currently no Extensions planned that would use this
     * functionality. Hence we check all the extensions after declarations and signatures are checked. This allows
     * extensions in which there are function, domain function and method applications.
     */
    p.extensions foreach checkExtension

    /* [2022-03-14 Alessandro]
     * The following block of checks must occur after declarations and signatures are checked, but the checks in the block
     * do not depend on each other. Note that extensions are checked beforehand, which allow function and method alike extensions.
     */
    p.domains foreach checkAxioms
    p.functions foreach checkBody
    p.predicates foreach checkBody
    p.methods foreach checkBody


    /* Report any domain type that couldn't be resolved */
    /* Alex suggests replacing *all* these occurrences by one arbitrary type */
    p visit {
      case dt: PDomainType if dt.isUndeclared => messages ++= FastMessaging.message(dt, s"found undeclared type ${dt.domain.name}")
    }
  }

  def checkMember(m: PScope)(fcheck: => Unit): Unit = {
    val oldCurMember = curMember
    curMember = m
    fcheck
    curMember = oldCurMember
  }

  def checkDeclaration(m: PMethod): Unit = {
    checkMember(m) {
      (m.formalArgs ++ m.formalReturns) foreach (a => check(a.typ))
    }
  }

  def checkBody(m: PMethod): Unit = {
    checkMember(m) {
      m.pres.toSeq foreach (p => check(p.e, Bool))
      m.posts.toSeq foreach (p => check(p.e, Bool))
      m.body.foreach(check)
    }
  }

  def checkDeclaration(f: PFunction): Unit = {
    checkMember(f) {
      assert(curFunction == null)
      curFunction = f
      f.formalArgs foreach (a => check(a.typ))
      check(f.typ)
      curFunction = null
    }
  }

  def checkBody(f: PFunction): Unit = {
    checkMember(f) {
      assert(curFunction == null)
      curFunction = f
      f.pres.toSeq foreach (p => check(p.e, Bool))
      resultAllowed = true
      f.posts.toSeq foreach (p => check(p.e, Bool))
      f.body.map(_.inner).foreach(check(_, f.typ.resultType)) //result in the function body gets the error message somewhere else
      resultAllowed = false
      curFunction = null
    }
  }

  def checkDeclaration(p: PPredicate): Unit = {
    checkMember(p) {
      p.formalArgs foreach (a => check(a.typ))
    }
  }

  def checkBody(p: PPredicate): Unit = {
    checkMember(p) {
      p.body.map(_.e.inner).foreach(check(_, Bool))
    }
  }

  def check(f: PFields): Unit = {
    checkMember(f) {
      f.fields.toSeq foreach (fd => {
        fd.decl = Some(f)
        check(fd.typ)
      })
    }
  }

  def checkFunctions(d: PDomain): Unit = {
    checkMember(d) {
      d.members.funcs.toSeq foreach check
    }
  }

  def checkAxioms(d: PDomain): Unit = {
    checkMember(d) {
      d.members.axioms.toSeq foreach check
    }
  }

  def check(a: PAxiom): Unit = {
    checkMember(a) {
      check(a.exp.e.inner, Bool)
    }
  }

  def check(f: PDomainFunction): Unit = {
    check(f.typ)
    f.formalArgs foreach (a => check(a.typ))
  }

  def check(stmt: PStmt): Unit = {
    stmt match {
      case PAnnotatedStmt(_, s) =>
        check(s)
      case s@PSeqn(ss) =>
        checkMember(s) {
          ss.inner.toSeq foreach check
        }
      case PFold(_, e) =>
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be folded")
        check(e, Bool)
      case PUnfold(_, e) =>
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be unfolded")
        check(e, Bool)
      case PPackageWand(_, e, proofScript) =>
        check(e, Wand)
        checkMagicWand(e)
        proofScript foreach check
      case PApplyWand(_, e) =>
        check(e, Wand)
        checkMagicWand(e)
      case PExhale(_, e) =>
        check(e, Bool)
      case PAssert(_, e) =>
        check(e, Bool)
      case PInhale(_, e) =>
        check(e, Bool)
      case PAssume(_, e) =>
        check(e, Bool)
      case assign: PAssign =>
        checkAssign(assign)
      case PLabel(_, _, invs) =>
        invs.toSeq foreach (i => check(i.e, Bool))
      case PGoto(_, _) =>
      case PIf(_, cond, thn, els) =>
        check(cond, Bool)
        check(thn)
        els foreach check
      case PElse(_, els) =>
        check(els)
      case PWhile(_, cond, invs, body) =>
        check(cond, Bool)
        invs.toSeq foreach (inv => check(inv.e, Bool))
        check(body)
      case v: PVars =>
        v.vars.toSeq foreach (v => check(v.typ))
        v.assign foreach checkAssign
      case _: PDefine =>
        /* Should have been removed right after parsing */
        sys.error(s"Unexpected node $stmt found")
      case PQuasihavoc(_, lhs, e) =>
        checkHavoc(stmt, lhs.map(_._1), e)
      case havoc@PQuasihavocall(_, vars, _, lhs, e) =>
        vars.toSeq foreach (v => check(v.typ))
        // update the curMember, which contains quantified variable information
        val oldCurMember = curMember
        curMember = havoc
        // Actually type check the havoc
        checkHavoc(stmt, lhs.map(_._1), e)
        // restore the previous curMember
        curMember = oldCurMember

      case t: PExtender => t.typecheck(this, names).getOrElse(Nil) foreach (message =>
        messages ++= FastMessaging.message(t, message))
      case _: PSkip =>
    }
  }

  def checkAssign(stmt: PAssign): Unit = {
    // Check targets
    stmt.targets.toSeq foreach {
      case idnuse: PIdnUse =>
        idnuse.assignUse = true
        names.definition(curMember)(idnuse) match {
          case Some(decl: PAssignableVarDecl) =>
            check(idnuse, decl.typ)
          case _ =>
            messages ++= FastMessaging.message(idnuse, "expected an assignable identifier as lhs")
        }
      case fa@PFieldAccess(_, _, field) =>
        field.assignUse = true
        names.definition(curMember)(field, Some(PFields.getClass)) match {
          case Some(PFieldDecl(_, typ)) =>
            check(fa, typ)
          case _ =>
            messages ++= FastMessaging.message(field, "expected a field as lhs")
        }
      case call: PCall => sys.error(s"Unexpected node $call found")
    }
    // Check rhs
    stmt match {
      case PAssign(targets, _, c@PCall(func, _, _)) if names.definition(curMember)(func).get.isInstanceOf[PMethod] =>
        val m = names.definition(curMember)(func).get.asInstanceOf[PMethod]
        val formalArgs = m.formalArgs
        val formalTargets = m.formalReturns
        c.methodDecl = Some(m)
        func.decl = Some(m)
        formalArgs.foreach(fa => check(fa.typ))
        if (formalArgs.length != c.args.length) {
          messages ++= FastMessaging.message(stmt, "wrong number of arguments")
        } else if (formalTargets.length != targets.length) {
          messages ++= FastMessaging.message(stmt, "wrong number of targets")
        } else {
          for ((formal, actual) <- (formalArgs zip c.args) ++ (formalTargets zip targets.toSeq)) {
            check(actual, formal.typ)
          }
        }
      case PAssign(targets, _, PNewExp(_, fieldsOpt)) if targets.length == 1 =>
        check(targets.head, Ref)
        fieldsOpt.inner foreach (fds => acceptAndCheckTypedEntity[PFieldDecl, Nothing](fds.toSeq, "expected a field as argument"))
      case PAssign(targets, _, rhs) if targets.length == 1 => check(rhs, targets.head.typ)
      // Case `targets.length != 1`:
      case _ => messages ++= FastMessaging.message(stmt, "expected a method call")
    }
  }

  def checkHavoc(stmt: PStmt, lhs: Option[PExp], e: PExp): Unit = {
    // If there is a condition, make sure that it is a Bool
    if (lhs.nonEmpty) {
      check(lhs.get, Bool)
    }
    // Make sure that the rhs is a resource
    val havocError = "Havoc statement must take a field access, predicate, or wand"
    e match {
      case _: PFieldAccess => checkTopTyped(e, None)
      case pc: PCall =>
        check(e, Bool)
        // make sure that this is in fact a predicate
        if (!pc.isPredicate) {
          messages ++= FastMessaging.message(stmt, havocError)
        }
      case _: PMagicWandExp => check(e, Bool)
      case _ => messages ++= FastMessaging.message(stmt, havocError)
    }
  }

  def acceptNonAbstractPredicateAccess(exp: PExp, messageIfAbstractPredicate: String): Unit = {
    exp match {
      case acc: PAccPred if acc.loc.isInstanceOf[PCall] =>
        val idnuse = acc.loc.asInstanceOf[PCall].func
        val ad = names.definition(curMember)(idnuse)
        ad match {
          case Some(predicate: PPredicate) =>
            if (predicate.body.isEmpty) messages ++= FastMessaging.message(idnuse, messageIfAbstractPredicate)
          case _ => messages ++= FastMessaging.message(exp, "expected predicate access")
        }

      case _ => messages ++= FastMessaging.message(exp, "expected predicate access")
    }
  }

  def checkMagicWand(e: PExp): Unit = e match {
    case PBinExp(_, PReserved(PSymOp.Wand), _) =>
    case _ =>
      messages ++= FastMessaging.message(e, "expected magic wand")
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
    * @param idnUses      Identifier usages to check
    * @param errorMessage Error message in case one of the identifiers usages
    *                     does not refer to an appropriate subtype of
    *                     `TypedEntity`
    * @param handle       Handle pairs of current identifier usage and referenced
    *                     `TypedEntity`
    * @tparam T1 An accepted subtype of `TypedEntity`
    * @tparam T2 Another accepted subtype of `TypedEntity`
    *
    *            TODO: Generalise the method to take ClassTags T1, ..., TN.
    *            TODO: If only a single T is taken, let handle be (PIdnUse, T) => Unit
    */
  def acceptAndCheckTypedEntity[T1: ClassTag, T2: ClassTag]
  (idnUses: Seq[PIdnUse], errorMessage: => String): Unit = {

    /* TODO: Ensure that the ClassTags denote subtypes of TypedEntity */
    val acceptedClasses = Seq[Class[_]](classTag[T1].runtimeClass, classTag[T2].runtimeClass)

    idnUses.foreach { use =>
      val decl = names.definition(curMember)(use)

      if (decl.isDefined) {
        acceptedClasses.find(_.isInstance(decl.get)) match {
          case Some(_) =>
            val td = decl.get.asInstanceOf[PTypedDeclaration]
            if (use.isInstanceOf[PIdnUseExp])
              use.asInstanceOf[PIdnUseExp].typ = td.typ
            use.decl = Some(td)
          case None =>
            messages ++= FastMessaging.message(use, errorMessage)
        }
      } else {
        assert(!names.success)
      }
    }
  }

  def check(typ: PType): Unit = {
    typ match {
      case _: PWandType =>
        sys.error("unexpected use of internal typ")
      case PPrimitiv(_) =>
      /* Nothing to type check (or resolve) */
      case dt@PDomainType(_, _) if dt.isResolved =>
      /* Already resolved, nothing left to do */
      case dt@PDomainType(domain, args) =>
        assert(!dt.isResolved, "Only yet-unresolved domain types should be type-checked and resolved")

        args foreach (_.inner.toSeq foreach check)

        names.definition(curMember)(domain) match {
          case Some(PDomain(_, _, _, typVars, _, _)) =>
            ensure(args.map(_.inner.length) == typVars.map(_.inner.length), typ, "wrong number of type arguments")
            dt.kind = PDomainTypeKinds.Domain
          case Some(PTypeVarDecl(_)) =>
            dt.kind = PDomainTypeKinds.TypeVar
          case _ =>
            dt.kind = PDomainTypeKinds.Undeclared
        }

      case PSeqType(_, elemType) =>
        check(elemType.inner)
      case PSetType(_, elemType) =>
        check(elemType.inner)
      case PMultisetType(_, elemType) =>
        check(elemType.inner)
      case m: PMapType =>
        check(m.keyType)
        check(m.valueType)
      case PFunctionType(argTypes, resultType) =>
        argTypes map check
        check(resultType)
      case t: PExtender =>
        t.typecheck(this, names).getOrElse(Nil) foreach (message =>
          messages ++= FastMessaging.message(t, message))
      case PUnknown() =>
        messages ++= FastMessaging.message(typ, "expected concrete type, but found unknown type")
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
      case (Bool, PWandType()) => true
      case (PSeqType(_, e1), PSeqType(_, e2)) => isCompatible(e1.inner, e2.inner)
      case (PSetType(_, e1), PSetType(_, e2)) => isCompatible(e1.inner, e2.inner)
      case (PMultisetType(_, e1), PMultisetType(_, e2)) => isCompatible(e1.inner, e2.inner)
      case (m1: PMapType, m2: PMapType) => isCompatible(m1.keyType, m2.keyType) && isCompatible(m1.valueType, m2.valueType)
      case (PDomainType(domain1, args1), PDomainType(domain2, args2))
        if domain1 == domain2 && args1.map(_.inner.length) == args2.map(_.inner.length) =>
        (args1.toSeq.flatMap(_.inner.toSeq) zip args2.toSeq.flatMap(_.inner.toSeq)) forall (x => isCompatible(x._1, x._2))

      case (_: PExtender, _) => false // TBD: the equality function for two type variables
      case (_, _: PExtender) => false // TBD: the equality function for two type variables

      case _ => false
    }
  }

  /**
    * Type-check and resolve e and ensure that it has type expected.  If that is not the case, then an
    * error should be issued.
    */
  def composeAndAdd(pts1: PTypeSubstitution, pts2: PTypeSubstitution, pt1: PType, pt2: PType): Either[(PType, PType), PTypeSubstitution] = {
    val sharedKeys = pts1.keySet.intersect(pts2.keySet)
    if (sharedKeys.exists(p => pts1.get(p).get != pts2.get(p).get)) {
      /* no composed substitution if input substitutions do not match */
      val nonMatchingKey = sharedKeys.find(p => pts1.get(p).get != pts2.get(p).get).get
      return Left((pts1.get(nonMatchingKey).get, pts2.get(nonMatchingKey).get))
    }

    //composed substitution before add
    val cs = new PTypeSubstitution(
      pts1.map({ case (s: String, pt: PType) => s -> pt.substitute(pts2) }) ++
        pts2.map({ case (s: String, pt: PType) => s -> pt.substitute(pts1) }))
    cs.add(pt1, pt2)
  }

  /*
   * Parameters:
   * rlts: local substitutions, refreshed
   * argData: a sequence of tuples, one per op arguments, where
   *          _1 is the fresh local argument type
   *          _2 is the type of the argument expression
   *          _3 is the set of substitutions of the argument expression
   *          _4 is the argument expression itself (used to extract a precise position)
   * Returns:
   * Either a new type substitution (right case) or, in case of failure (left) a triple containing
   *          _1 the expected type
   *          _2 the found type
   *          _3 the argument that caused the failure
   */
  def unifySequenceWithSubstitutions(rlts: Seq[PTypeSubstitution],
                                     argData: scala.collection.immutable.Seq[(PType, PType, Seq[PTypeSubstitution], PExp)])
  : Either[(PType, PType, PExp), Seq[PTypeSubstitution]] = {
    var pss = rlts
    for (tri <- argData) {
      val current = (for (ps <- pss; aps <- tri._3)
        yield composeAndAdd(ps, aps, tri._1, tri._2))
      val allBad = current.forall(e => e.isLeft)
      if (allBad) {
        val badMatch = current.find(e => e.isLeft)
        val badTypes = badMatch.get.swap.toOption.get
        return Left(badTypes._1, badTypes._2, tri._4)
      }
      pss = current.flatMap(_.toOption)
    }
    Right(pss)
  }

  def ground(exp: PExp, pts: PTypeSubstitution): PTypeSubstitution = {
    pts.m.flatMap(kv => kv._2.freeTypeVariables &~ pts.m.keySet).foldLeft(pts)((ts, fv) => {
      messages ++= FastMessaging.message(exp,
        s"Unconstrained type parameter, substituting default type ${PTypeSubstitution.defaultType}.", error = false)
      ts.add(PTypeVar(fv), PTypeSubstitution.defaultType).toOption.get
    })
  }

  def selectAndGroundTypeSubstitution(exp: PExp, etss: collection.Seq[PTypeSubstitution]): PTypeSubstitution = {
    require(etss.nonEmpty)
    ground(exp, etss.head)
  }

  def typeError(exp: PExp) = {
    messages ++= FastMessaging.message(exp, s"Type error in the expression at ${exp.pos._1}")
  }

  def check(exp: PExp, expected: PType) = exp match {
    case t: PExtender => t.typecheck(this, names, expected).getOrElse(Nil) foreach (message =>
      messages ++= FastMessaging.message(t, message))

    case _ => checkTopTyped(exp, Some(expected))
  }

  def checkTopTyped(exp: PExp, oexpected: Option[PType]): Unit = {
    checkInternal(exp)
    if (exp.typ.isValidOrUndeclared && exp.typeSubstitutions.nonEmpty) {
      val etss = oexpected match {
        case Some(expected) if expected.isValidOrUndeclared => exp.typeSubstitutions.flatMap(_.add(exp.typ, expected).toOption)
        case _ => exp.typeSubstitutions
      }
      if (etss.nonEmpty) {
        val ts = selectAndGroundTypeSubstitution(exp, etss)
        exp.forceSubstitution(ts)
      } else {
        oexpected match {
          case Some(expected) =>
            val reportedActual = if (exp.typ.isGround) {
              exp.typ
            } else {
              exp.typ.substitute(selectAndGroundTypeSubstitution(exp, exp.typeSubstitutions))
            }
            messages ++= FastMessaging.message(exp,
              s"Expected type ${expected.pretty}, but found ${reportedActual.pretty} at the expression at ${exp.pos._1}")
          case None =>
            typeError(exp)
        }
      }
    }
  }

  def checkInternal(exp: PExp): Unit = {
    /**
      * Set the type of 'exp', and check that the actual type is allowed by one of the expected types.
      */
    def setType(actual: PType): Unit = {
      exp.typ = actual
    }

    /**
      * Issue an error for the node at 'n'. Also sets an error type for 'exp' to suppress
      * further warnings.
      *
      * TODO: Similar to Consistency.recordIfNot. Combine!
      */
    def issueError(n: PNode, m: String): Unit = {
      messages ++= FastMessaging.message(n, m)
      setErrorType() // suppress further warnings
    }

    /**
      * Sets an error type for 'exp' to suppress further warnings.
      */
    def setErrorType(): Unit = {
      setType(PUnknown()())
    }

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)


    //Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      //      require(rts.values.forall { case pdt: PDomainType if pdt.isTypeVar => true case _ => false })
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    def inAxiomScope(s: Option[PNode]): Boolean =
      s match {
        case Some(_: PAxiom) => true
        case Some(x) => inAxiomScope(x.parent)
        case None => false
      }

    var extraReturnTypeConstraint: Option[PType] = None

    exp match {
      /*
        An extra hook for extending the TypeChecker in case of expressions as this portion of the TypeChecker for expressions is
        accessible only when an expression is used inside another expression(an extremely frequent occurrence).
        The main aim is to give the plugin developer more options as to whether type checking with an expected return type
        is preferred or a simplistic approach.
       */

      case t: PExtender => t.typecheck(this, names).getOrElse(Nil) foreach (message =>
        messages ++= FastMessaging.message(t, message))
      case PAnnotatedExp(_, e) =>
        checkInternal(e)
        setType(e.typ)
      case psl: PSimpleLiteral=>
        psl match {
          case r@PResultLit(_) =>
            if (resultAllowed)
              setType(curFunction.typ.resultType)
            else
              issueError(r, "'result' can only be used in function postconditions")
          case _ =>
        }

      case poa: POpApp =>
        if (poa.typeSubstitutions.isEmpty) {
          poa.args.foreach(checkInternal)
          var nestedTypeError = !poa.args.forall(a => a.typ.isValidOrUndeclared)
          poa match {
            case pfa@PCall(func, _, explicitType) =>
              explicitType match {
                case Some((_, t)) =>
                  check(t)
                  if (!t.isValidOrUndeclared) nestedTypeError = true
                case None =>
              }
              val ad = names.definition(curMember)(func)
              ad match {
                case Some(fd: PAnyFunction) =>
                  func.decl = Some(fd)
                  pfa.funcDecl = Some(fd)
                  ensure(fd.formalArgs.length == pfa.args.length, pfa, "wrong number of arguments")
                  fd match {
                    case pfn: PFunction =>
                      checkMember(fd) {
                        check(fd.typ)
                        fd.formalArgs foreach (a => check(a.typ))
                      }
                      if (inAxiomScope(Some(pfa)) && pfn.pres.length != 0)
                        issueError(func, s"Cannot use function ${func.name}, which has preconditions, inside axiom")

                    case pdf: PDomainFunction =>
                      val domain = names.definition(curMember)(pdf.domainName).get.asInstanceOf[PDomain]
                      val typVars = domain.typVarsSeq
                      val fdtv = PTypeVar.freshTypeSubstitution((typVars map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                      pfa.domainTypeRenaming = Some(fdtv)
                      pfa._extraLocalTypeVariables = (typVars map (tv => PTypeVar(tv.idndef.name))).toSet
                      extraReturnTypeConstraint = explicitType.map(_._2)
                    case _: PPredicate =>
                  }
                case _ =>
                  issueError(func, "expected function or predicate ")
              }

            case pu: PUnfolding =>
              if (!isCompatible(pu.acc.loc.typ, Bool)) {
                messages ++= FastMessaging.message(pu, "expected predicate access")
              }
              acceptNonAbstractPredicateAccess(pu.acc, "abstract predicates cannot be unfolded")

            case PApplying(_, wand, _, _) =>
              checkMagicWand(wand)

            // We checked that the `rcv` is valid above with `poa.args.foreach(checkInternal)`
            case PFieldAccess(_, _, idnuse) =>
              acceptAndCheckTypedEntity[PFieldDecl, Nothing](Seq(idnuse), "expected field")

            case acc: PAccPred =>
              acc.loc match {
                case _: PFieldAccess =>
                case pc: PCall if pc.isPredicate =>
                case loc =>
                  issueError(loc, "specified location is not a field nor a predicate")
              }

            case pecl: PEmptyCollectionLiteral if !pecl.pElementType.isValidOrUndeclared =>
              check(pecl.pElementType)

            case pem: PEmptyMap if !pem.pKeyType.isValidOrUndeclared || !pem.pValueType.isValidOrUndeclared =>
              if (!pem.pKeyType.isValidOrUndeclared)
                check(pem.pKeyType)
              if (!pem.pValueType.isValidOrUndeclared)
                check(pem.pValueType)

            case _ =>
          }

          val ltr = getFreshTypeSubstitution(poa.localScope.toList) //local type renaming - fresh versions
          val rlts = poa.signatures map (ts => refreshWith(ts, ltr)) //local substitutions refreshed
          val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type
          // Continue only if there was no error in the arguments
          if (rlts.nonEmpty && poa.args.forall(_.typeSubstitutions.nonEmpty) && !nestedTypeError) {
            val flat = poa.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
            // the quadruples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, expression)
            val argData = flat.indices.map(i => (flat(i), poa.args(i).typ, poa.args(i).typeSubstitutions.distinct.toSeq, poa.args(i))) ++
              (
                extraReturnTypeConstraint match {
                  case None => Nil
                  case Some(t) => Seq((rrt, t, List(PTypeSubstitution.id), poa))
                }
                )
            val unifiedSequence = unifySequenceWithSubstitutions(rlts, argData)
            if (unifiedSequence.isLeft && poa.typeSubstitutions.isEmpty) {
              val problem = unifiedSequence.left.toOption.get
              messages ++= FastMessaging.message(problem._3,
                s"Expected type ${problem._1.pretty}, but found ${problem._2.pretty} at the expression at ${problem._3.pos._1}.")
            } else {
              poa.typeSubstitutions ++= unifiedSequence.toOption.get
              val ts = poa.typeSubstitutions.distinct
              poa.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
            }
          } else {
            poa.typeSubstitutions.clear()
            // Try to get a correct type even though the
            val ts = rlts.map(rrt.substitute(_)).distinct
            if (ts.size == 1) {
              poa.typeSubstitutions += rlts.find(_.contains(rrt)).get
              poa.typ = ts.head
            } else
              poa.typ = PUnknown()()
          }
        }

      case piu: PIdnUse =>
        acceptAndCheckTypedEntity[PAnyVarDecl, Nothing](Seq(piu), "expected variable identifier")

      case pl@PLet(_, variable, _, e, _, ns) =>
        val oldCurMember = curMember
        curMember = ns
        checkInternal(e)
        variable.typ = e.typ
        checkInternal(ns.body)
        pl.typ = ns.body.typ
        curMember = oldCurMember

      case pq: PForPerm =>
        val oldCurMember = curMember
        curMember = pq
        pq.boundVars foreach (v => check(v.typ))
        check(pq.body, Bool)
        checkInternal(pq.accessRes.inner)
        pq.triggers foreach (_.exp.inner.toSeq foreach (tpe => checkTopTyped(tpe, None)))
        pq._typeSubstitutions = pq.body.typeSubstitutions.toList.distinct
        pq.typ = Bool
        curMember = oldCurMember

      case pq: PQuantifier =>
        val oldCurMember = curMember
        curMember = pq
        pq.boundVars foreach (v => check(v.typ))
        check(pq.body, Bool)
        pq.triggers foreach (_.exp.inner.toSeq foreach (tpe => checkTopTyped(tpe, None)))
        pq._typeSubstitutions = pq.body.typeSubstitutions.toList.distinct
        pq.typ = Bool
        curMember = oldCurMember
      
      case pne: PNewExp => issueError(pne, s"unexpected use of `new` as an expression")
    }
  }

  def checkExtension(e: PExtender): Unit = e.typecheck(this, names).getOrElse(Nil) foreach (message =>
    messages ++= FastMessaging.message(e, message))

  /**
    * If b is false, report an error for node.
    */
  def ensure(b: Boolean, node: PNode, msg: String): Unit = {
    if (!b) messages ++= FastMessaging.message(node, msg)
  }
}

/**
  * Resolves identifiers to their declaration.
  */
case class NameAnalyser() {

  /** To record error messages */
  var messages: FastMessaging.Messages = Nil
  def success: Boolean = messages.isEmpty || messages.forall(m => !m.error)

  /** Resolves the declaration to which the given identifier `idnuse` refers.
    *
    * If `member` is not null then the identifier will first be looked up in
    * the scope defined by the member. If it fails (or if the member is null),
    * the wider scope will be considered.
    *
    * In order to resolve name clashes, e.g., if the identifier is expected to
    * refer to a field, but there is a local variable with the same name in the
    * member scope that shadows the field, then the `expected` class can be
    * provided (e.g., `PFields`), with the result that the shadowing local
    * variable will be ignored because its class (`PVars`) doesn't
    * match.
    *
    * @param member   Current scope in which to start the resolving.
    * @param idnuse   Identifier that is to be resolved.
    * @param expected Expected class of the entity.
    * @return Resolved entity of expected type, or None if no entity of that type was found.
    */
  def definition(member: PScope)(idnuse: PIdnUse, expected: Option[Class[_]] = None): Option[PDeclaration] = {
    if (member == null) {
      globalDeclarationMap.get(idnuse.name)
    } else {
      // lookup in method map first, and otherwise in the general one
      val entity =
        localDeclarationMaps.get(member.scopeId).get.get(idnuse.name) match {
          case None =>
            globalDeclarationMap.get(idnuse.name)
          case Some(foundEntity) =>
            if (expected.isDefined && foundEntity.getClass != expected.get) {
              val globalResult = globalDeclarationMap.get(idnuse.name)
              if (globalResult.isDefined && globalResult.get.getClass == expected.get) {
                globalResult
              } else {
                // error will reported by caller.
                None
              }
            } else {
              Some(foundEntity)
            }
        }

      entity
    }
  }

  def reset(): Unit = {
    globalDeclarationMap.clear()
    localDeclarationMaps.clear()
    universalDeclarationMap.clear()
    namesInScope.clear()
  }

  private val globalDeclarationMap = mutable.HashMap[String, PDeclaration]()
  private val universalDeclarationMap = mutable.HashMap[String, PDeclaration]()

  /* [2014-11-13 Malte] Changed localDeclarationMaps to be a map from PScope.Id
   * instead of from PScope directly. This was necessary in order to support
   * changing PScopes during type-checking, e.g., when changing the type of a
   * variable bound by a let-expression. This change (potentially) affects the
   * hashcode of the let-expression (which is a PScope), which in turn affects
   * localDeclarationMaps because such that the value stored for scope cannot
   * be retrieved anymore.
   */
  private val localDeclarationMaps = mutable.HashMap[PScope.Id, mutable.HashMap[String, PDeclaration]]()

  private val namesInScope = mutable.Set.empty[String]

  private def clearUniversalDeclarationsMap(): Unit = {
    universalDeclarationMap.map { k =>
      globalDeclarationMap.put(k._1, k._2)
      localDeclarationMaps.map { l =>
        l._2.put(k._1, k._2)
      }
    }
  }

  private def check(n: PNode, target: Option[PNode]): Unit = {
    var curMember: PScope = null

    def getMap(d: PNode): mutable.HashMap[String, PDeclaration] =
      d match {
        case _: PUniversalDeclaration => universalDeclarationMap
        case _: PGlobalDeclaration => globalDeclarationMap
        case _ => getCurrentMap
      }

    def getCurrentMap: mutable.HashMap[String, PDeclaration] =
      if (curMember == null) globalDeclarationMap else localDeclarationMaps.get(curMember.scopeId).get

    val scopeStack = mutable.Stack[PScope]()

    val nodeDownNameCollectorVisitor = new PartialFunction[PNode, Unit] {
      def apply(n: PNode) = {
        if (n == target.orNull)
          namesInScope ++= getCurrentMap.map(_._1)
        n match {
          case d: PDeclaration =>
            val map = getMap(d)
            map.get(d.idndef.name) match {
              case Some(m: PMember) if d eq m =>
              // We re-encountered a member we already looked at in the previous run.
              // This is expected, nothing to do.
              case Some(e: PDeclaration) =>
                messages ++= FastMessaging.message(d.idndef, "Duplicate identifier `" + e.idndef.name + "' at " + e.idndef.pos._1 + " and at " + d.idndef.pos._1)
              case None =>
                globalDeclarationMap.get(d.idndef.name) match {
                  case Some(e: PDeclaration) =>
                    if (!(d.parent.isDefined && d.parent.get.isInstanceOf[PDomainFunction]))
                      messages ++= FastMessaging.message(d.idndef, "Identifier shadowing `" + e.idndef.name + "' at " + e.idndef.pos._1 + " and at " + d.idndef.pos._1)
                  case None =>
                }
                map.put(d.idndef.name, d)
            }
          case i: PIdnUse =>
            // look up in both maps (if we are not in a method currently, we look in the same map twice, but that is ok)
            val resolved = getCurrentMap.getOrElse(i.name, globalDeclarationMap.getOrElse(i.name, PUnknownEntity()))
            (i.parent, resolved) match {
              case (Some(parent), PUnknownEntity()) =>
                if (!parent.isInstanceOf[PDomainType] && !parent.isInstanceOf[PGoto] &&
                  !(parent.isInstanceOf[POldExp] && parent.asInstanceOf[POldExp].label.map(_ == i).getOrElse(false)) &&
                  !(i.name == LabelledOld.LhsOldLabel && parent.isInstanceOf[POldExp] && parent.asInstanceOf[POldExp].label.isDefined)) {
                  messages ++= FastMessaging.message(i, s"identifier ${i.name} not defined.")
                }
              // domain types can also be type variables, which need not be declared
              // goto and state labels may exist out of scope (but must exist in method, this is checked in final AST in checkIdentifiers)
              case (None, _) =>
              case _ =>
            }
          case _ =>
        }

        n match {
          case s: PScope =>
            val localDeclarations =
              if (curMember == null)
                mutable.HashMap[String, PDeclaration]()
              else
                localDeclarationMaps.getOrElse(curMember.scopeId, mutable.HashMap[String, PDeclaration]()).clone()

            localDeclarationMaps.put(s.scopeId, localDeclarations)
            scopeStack.push(curMember)
            curMember = s
          case _ =>
        }
      }

      def isDefinedAt(n: PNode) = {
        n match {
          case _: PDeclaration => true
          case _: PScope => true
          case _: PIdnUse => true
          case _ => target.isDefined
        }
      }
    }

    val nodeUpNameCollectorVisitor = new PartialFunction[PNode, Unit] {
      def apply(n: PNode) = {
        n match {
          case _: PScope =>
            curMember = scopeStack.pop()
          case _ =>
        }
      }

      def isDefinedAt(n: PNode) = {
        n match {
          case _: PScope => true
          case _ => false
        }
      }
    }

    n match {
      case prog: PProgram =>
        // find all global names first
        for (d <- prog.domains) {
          nodeDownNameCollectorVisitor(d)
          d.members.funcs.toSeq.foreach(f => {
            nodeDownNameCollectorVisitor(f);
            nodeUpNameCollectorVisitor(f)
          })
          nodeUpNameCollectorVisitor(d)
        }
        prog.fields.foreach(f => f.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))
        prog.functions.foreach(f => {
          nodeDownNameCollectorVisitor(f);
          nodeUpNameCollectorVisitor(f)
        })
        prog.predicates.foreach(f => {
          nodeDownNameCollectorVisitor(f);
          nodeUpNameCollectorVisitor(f)
        })
        prog.methods.foreach(m => {
          nodeDownNameCollectorVisitor(m);
          nodeUpNameCollectorVisitor(m)
        })
        prog.extensions.foreach(e => e.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))

        // now completely walk through all axioms, functions, predicates, and methods
        prog.domains.foreach(d => d.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))
        prog.functions.foreach(f => f.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))
        prog.predicates.foreach(f => f.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))
        prog.methods.foreach(m => m.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor))

      case _ =>
        // find all declarations
        n.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor)
    }
    clearUniversalDeclarationsMap()
  }

  def run(p: PProgram): Boolean = {
    check(p, None)
    success
  }

  def namesInScope(n: PNode, target: Option[PNode] = None): Set[String] = {
    check(n, target)
    (namesInScope ++ globalDeclarationMap.map(_._1)).toSet
  }
}
