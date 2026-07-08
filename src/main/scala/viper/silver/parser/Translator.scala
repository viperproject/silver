// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.FastMessaging
import viper.silver.ast.utility._
import viper.silver.ast.{SourcePosition, _}
import viper.silver.dependencyAnalysis._
import viper.silver.plugin.standard.adt.{Adt, AdtType}

import scala.collection.mutable
import scala.language.implicitConversions

/**
 * Takes an abstract syntax tree after parsing is done and translates it into
 * a Viper abstract syntax tree.
 *
 * [2014-05-08 Malte] The current architecture of the resolver makes it hard
 * to detect all malformed ASTs. It is, for example, hard to detect that an
 * expression "f > 0", where f is an int-typed field, is malformed.
 * The translator can thus not assume that the input tree is completely
 * wellformed, and in cases where a malformed tree is detected, it does not
 * return a tree, but instead, records error messages using the
 * Messaging feature.
 */
case class Translator(program: PProgram) {
  def translate: Option[Program] /*(Program, Seq[Messaging.Record])*/ = {
    // assert(TypeChecker.messagecount == 0, "Expected previous phases to succeed, but found error messages.") // AS: no longer sharing state with these phases

    val (pdomains, pfields, pfunctions, ppredicates, pmethods, pextensions) =
      (program.domains, program.fields, program.functions, program.predicates, program.methods, program.extensions)

    /* [2022-03-14 Alessandro] Domain signatures need no be translated first, since signatures of other declarations
      * like domain functions, and ordinary functions might depend on the domain signature. Especially this is the case
      * when signatures contain user-defined domain types. The same applies for extensions since they might introduce
      * new top-level declarations that behave similar as domains.
      */
    pdomains foreach translateMemberSignature
    pextensions foreach translateMemberSignature

    /* [2022-03-14 Alessandro] Following signatures can be translated independently of each other but must be translated
      * after signatures of domains and extensions because of the above mentioned reasons.
      */
    pdomains flatMap (_.funcs) foreach translateMemberSignature
    (pfields ++ pfunctions ++ ppredicates ++ pmethods) foreach translateMemberSignature

    /* [2022-03-14 Alessandro] After the signatures are translated, the actual full translations can be done
      * independently of each other.
      */
    val extensions = pextensions map translate
    val domain = (pdomains map translate) ++ extensions filter (t => t.isInstanceOf[Domain])
    val fields = (pfields flatMap (_.fields.toSeq map translate)) ++ extensions filter (t => t.isInstanceOf[Field])
    val functions = (pfunctions map translate) ++ extensions filter (t => t.isInstanceOf[Function])
    val predicates = (ppredicates map translate) ++ extensions filter (t => t.isInstanceOf[Predicate])
    val methods = (pmethods map translate) ++ extensions filter (t => t.isInstanceOf[Method])



    val finalProgram = ImpureAssumeRewriter.rewriteAssumes(Program(domain.asInstanceOf[Seq[Domain]], fields.asInstanceOf[Seq[Field]],
            functions.asInstanceOf[Seq[Function]], predicates.asInstanceOf[Seq[Predicate]], methods.asInstanceOf[Seq[Method]],
                (extensions filter (t => t.isInstanceOf[ExtensionMember])).asInstanceOf[Seq[ExtensionMember]])(program))

    finalProgram.deepCollect {
      case fp: ForPerm => Consistency.checkForPermArguments(fp, finalProgram)
      case trig: Trigger => Consistency.checkTriggers(trig, finalProgram)
    }

    if (Consistency.messages.isEmpty) Some(finalProgram) // all error messages generated during translation should be Consistency messages
    else None
  }

  private def translate(t: PExtender): Member = {
    t.translateMember(this)
  }

  private def translate(m: PMethod): Method = m match {
    case PMethod(_, _, idndef, _, _, pres, posts, body) =>
      val m = findMethod(idndef)

      val newBody = body.map(actualBody => stmt(actualBody).asInstanceOf[Seqn])

      val postconditionType = if(body.isDefined) DependencyType.make(AssumptionType.ImplicitPostcondition) else DependencyType.make(AssumptionType.ExplicitPostcondition)

      val finalMethod = m.copy(pres = pres.toSeq map (p => exp(p.e, Some(DependencyType.make(AssumptionType.Precondition)))), posts = posts.toSeq map (p => exp(p.e, Some(postconditionType))), body = newBody)(m.pos, m.info, m.errT)

      members(m.name) = finalMethod

      finalMethod
  }

  private def translate(d: PDomain): Domain = d match {
    case pd@PDomain(_, _, name, _, interpretation, _) =>
      val d = findDomain(name)
      val dd = d.copy(functions = pd.funcs map (f => findDomainFunction(f.idndef)),
        axioms = pd.axioms map translate, interpretations = interpretation.map(_.interps))(d.pos, d.info, d.errT)
      members(d.name) = dd
      dd
  }

  private def translate(a: PAxiom): DomainAxiom = {

    def attachMeta(createAxiom: (Position, Info, String, ErrorTrafo) => DomainAxiom, _pos: Position, _info: Info, _domainName: String, _errT: ErrorTrafo = NoTrafos): DomainAxiom = {
      val tmpAxiom = createAxiom(_pos, _info, _domainName, _errT)
      val finalInfo = ConsInfo(tmpAxiom.info, ConsInfo(ConsInfo(AnalysisSourceInfo.createAnalysisSourceInfo(tmpAxiom.exp), DependencyTypeInfo(DependencyType.Axiom)), SimpleDependencyAnalysisJoin(AnalysisSourceInfo.createAnalysisSourceInfo(tmpAxiom.exp), JoinType.Source, EdgeType.Down)))
      createAxiom(_pos, finalInfo, _domainName, _errT)
    }

    a match {
      case pa@PAxiom(anns, _, Some(name), e) =>
        attachMeta(NamedDomainAxiom(name.name, exp(e.e.inner, Some(DependencyType.Axiom))), a, Translator.toInfo(anns, pa), _domainName = pa.domain.idndef.name)
      case pa@PAxiom(anns, _, None, e) =>
        attachMeta(AnonymousDomainAxiom(exp(e.e.inner, Some(DependencyType.Axiom))), a, Translator.toInfo(anns, pa), _domainName = pa.domain.idndef.name)
    }
  }

  private def translate(f: PFunction): Function = f match {
    case PFunction(_, _, idndef, _, _, _, pres, posts, body) =>
      val f = findFunction(idndef)
      val postconditionType = if(body.isDefined) DependencyType.make(AssumptionType.ImplicitPostcondition) else DependencyType.make(AssumptionType.ExplicitPostcondition)
      val ff = f.copy( pres = pres.toSeq map (p => exp(p.e, Some(DependencyType.make(AssumptionType.Precondition)))), posts = posts.toSeq map (p => exp(p.e, Some(postconditionType))), body = body map (_.e.inner) map (exp(_, Some(DependencyType.make(AssumptionType.FunctionBody)))))(f.pos, f.info, f.errT)
      members(f.name) = ff
      ff
  }

  private def translate(p: PPredicate): Predicate = p match {
    case PPredicate(_, _, idndef, _, body) =>
      val p = findPredicate(idndef)
      val pp = p.copy(body = body map (_.e.inner) map (exp(_, Some(DependencyType.Rewrite))))(p.pos, p.info, p.errT)
      members(p.name) = pp
      pp
  }

  private def translate(f: PFieldDecl) = findField(f.idndef)

  protected val members: mutable.Map[String, Node] = collection.mutable.HashMap[String, Node]()
  def getMembers() = members
  /**
    * Translate the signature of a member, so that it can be looked up later.
    *
    * TODO: Get rid of this method!
    *         - Passing lots of null references is just asking for trouble
    *         - It should no longer be necessary to have this lookup table because, e.g. a
    *           method call no longer needs the method node, the method name (as a string)
    *           suffices
    */
  private def translateMemberSignature(p: PMember): Unit = p.declares foreach { decl =>
    val pos = decl
    val name = decl.idndef.name
    val t = decl match {
      case pf@PFieldDecl(_, _, typ) =>
        Field(name, ttyp(typ))(pos, Translator.toInfo(p.annotations, pf))
      case pf@PFunction(_, _, _, _, _, typ, _, _, _) =>
        Function(name, pf.formalArgs map liftArgDecl, ttyp(typ), null, null, null)(pos, Translator.toInfo(p.annotations, pf))
      case pdf@PDomainFunction(_, unique, _, _, _, _, typ, interp) =>
        DomainFunc(name, pdf.formalArgs map liftAnyArgDecl, ttyp(typ), unique.isDefined, interp.map(_.i.str))(pos, Translator.toInfo(p.annotations, pdf), pdf.domain.idndef.name)
      case pd@PDomain(_, _, _, typVars, interp, _) =>
        Domain(name, null, null, typVars map (_.inner.toSeq map (t => TypeVar(t.idndef.name))) getOrElse Nil, interp.map(_.interps))(pos, Translator.toInfo(p.annotations, pd))
      case pp: PPredicate =>
        Predicate(name, pp.formalArgs map liftArgDecl, null)(pos, Translator.toInfo(p.annotations, pp))
      case pm: PMethod =>
        Method(name, pm.formalArgs map liftArgDecl, pm.formalReturns map liftReturnDecl, null, null, null)(pos, Translator.toInfo(p.annotations, pm))
    }
    members.put(decl.idndef.name, t)
  }

  private def translateMemberSignature(p: PExtender): Unit ={
    p match {
      case _: PMember =>
        val l = p.translateMemberSignature(this)
        members.put(l.name, l)
    }
  }

  // helper methods that can be called if one knows what 'id' refers to
  private def findDomain(id: PIdentifier) = members(id.name).asInstanceOf[Domain]
  private def findField(id: PIdentifier) = members(id.name).asInstanceOf[Field]
  private def findFunction(id: PIdentifier) = members(id.name).asInstanceOf[Function]
  private def findDomainFunction(id: PIdentifier) = members(id.name).asInstanceOf[DomainFunc]
  private def findPredicate(id: PIdentifier) = members(id.name).asInstanceOf[Predicate]
  private def findMethod(id: PIdentifier) = members(id.name).asInstanceOf[Method]

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  def stmt(pStmt: PStmt): Stmt = {

    val pos = pStmt
    val (s, annotations) = extractAnnotationFromStmt(pStmt)
    val sourcePNodeInfo = SourcePNodeInfo(pStmt)
    val info = if (annotations.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotations))

    def attachMeta(createStmt: (Position, Info, ErrorTrafo) => Stmt, _pos: Position = pos, _info: Info = info, _errT: ErrorTrafo = NoTrafos): Stmt = {
      val tmpStmt = createStmt(_pos, _info, _errT)
      val finalInfo = MakeInfoPair(MakeInfoPair(AnalysisSourceInfo.createAnalysisSourceInfo(tmpStmt), DependencyTypeInfo.getDependencyTypeInfo(tmpStmt)), tmpStmt.info)
      createStmt(_pos, finalInfo, _errT)
    }

    s match {
      case PAssign(targets, _, PCall(method, args, _)) if members(method.name).isInstanceOf[Method] =>
        methodCallAssign(s, targets.toSeq, ts => attachMeta(MethodCall(findMethod(method), args.inner.toSeq map exp, ts)))
      case PAssign(targets, _, _) if targets.length != 1 =>
        sys.error(s"Found non-unary target of assignment")
      case PAssign(targets, _, PNewExp(_, fieldsOpt)) =>
        val fields = fieldsOpt.inner match {
          // Note that this will not use any fields that extensions declare
          case Left(_) => program.fields flatMap (_.fields.toSeq map translate)
          case Right(pfields) => pfields.toSeq map findField
        }
        methodCallAssign(s, Seq(targets.head), lv => attachMeta(NewStmt(lv.head, fields)))
      case PAssign(PDelimited(idnuse: PIdnUseExp), _, rhs) =>
        attachMeta(LocalVarAssign(LocalVar(idnuse.name, ttyp(idnuse.decl.get.asInstanceOf[PAssignableVarDecl].typ))(pos, SourcePNodeInfo(idnuse)), exp(rhs)))
      case PAssign(PDelimited(field: PFieldAccess), _, rhs) =>
        attachMeta(FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnref))(field, SourcePNodeInfo(field)), exp(rhs)))
      case lv: PVars =>
        // there are no declarations in the Viper AST; rather they are part of the scope signature
        lv.assign map stmt getOrElse Statements.EmptyStmt
      case PSeqn(ss) =>
        val seqn = ss.inner.toSeq
        val plocals = seqn.collect {
          case l: PVars => Some(l)
          case _ => None
        }
        val locals = plocals.flatten.flatMap {
          case p@PVars(_, vars, _) => vars.toSeq.map(v => LocalVarDecl(v.idndef.name, ttyp(v.typ))(p, SourcePNodeInfo(v)))
        }
        attachMeta(Seqn(seqn filterNot (_.isInstanceOf[PSkip]) map stmt, locals))
      case PFold(_, e) =>
        attachMeta(Fold(exp(e, Some(DependencyType.Rewrite)).asInstanceOf[PredicateAccessPredicate]))
      case PUnfold(_, e) =>
        attachMeta(Unfold(exp(e, Some(DependencyType.Rewrite)).asInstanceOf[PredicateAccessPredicate]))
      case PPackageWand(_, e, proofScript) =>
        val wand = exp(e, Some(DependencyType.Rewrite)).asInstanceOf[MagicWand]
        attachMeta(Package(wand, proofScript map (stmt(_).asInstanceOf[Seqn]) getOrElse Statements.EmptyStmt))
      case PApplyWand(_, e) =>
        attachMeta(Apply(exp(e, Some(DependencyType.Rewrite)).asInstanceOf[MagicWand]))
      case PInhale(_, e) =>
        attachMeta(Inhale(exp(e, Some(DependencyType.ExplicitAssumption))))
      case PAssume(_, e) =>
        attachMeta(Assume(exp(e, Some(DependencyType.ExplicitAssumption))))
      case PExhale(_, e) =>
        attachMeta(Exhale(exp(e, Some(DependencyType.ExplicitAssertion))))
      case PAssert(_, e) =>
        attachMeta(Assert(exp(e, Some(DependencyType.ExplicitAssertion))))
      case PLabel(_, name, invs) =>
        attachMeta(Label(name.name, invs.toSeq map (_.e) map exp))
      case PGoto(_, label) =>
        attachMeta(Goto(label.name))
      case PIf(_, cond, thn, els) =>
        attachMeta(If(exp(cond.inner, Some(DependencyType.PathCondition)), stmt(thn).asInstanceOf[Seqn], els map (stmt(_) match {
          case s: Seqn => s
          case s => Seqn(Seq(s), Nil)(s.pos, s.info)
        }) getOrElse Statements.EmptyStmt))
      case PElse(_, els) => stmt(els)
      case PWhile(_, cond, invs, body) =>
        attachMeta(While(exp(cond.inner, Some(DependencyType.PathCondition)), invs.toSeq map (inv => exp(inv.e, Some(DependencyType.Invariant))), stmt(body).asInstanceOf[Seqn]))
      case PQuasihavoc(_, lhs, e) =>
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        attachMeta(Quasihavoc(newLhs, newE))
      case PQuasihavocall(_, vars, _, lhs, e) =>
        val newVars = vars.toSeq map liftLogicalDecl
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        attachMeta(Quasihavocall(newVars, newLhs, newE))
      case t: PExtender =>
        val stmt = t.translateStmt(this)
        stmt.withMeta(stmt.pos, MakeInfoPair(MakeInfoPair(AnalysisSourceInfo.createAnalysisSourceInfo(stmt), DependencyTypeInfo.getDependencyTypeInfo(stmt)), stmt.info), stmt.errT)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }

  }

  /**
    * Translates a simple PAst `a, b, c := methodCall(...)` to an Ast `a, b, c := methodCall(...)`. But if any
    * targets are field accesses, then the translation is from `(exprA).f, b, (exprC).g := methodCall(...)` to
    * ```
    * {(scopedDecls: _receiver0, _target0, _receiver2, _target2)
    *   _receiver0 := exprA
    *   _receiver2 := exprC
    *   _target0, b, _target2 := methodCall(...)
    *   _receiver0.f := _target0
    *   _receiver2.g := _target2
    * }
    * ```
    */
  def methodCallAssign(errorNode: PNode, targets: Seq[PExp with PAssignTarget], assign: Seq[LocalVar] => Stmt): Stmt = {
    val tTargets = targets map exp
    val ts = tTargets.zipWithIndex.map {
      case (lv: LocalVar, _) => (None, lv)
      case (fa: FieldAccess, i) => {
        // --- Before the call ---
        val rcvDecl = LocalVarDecl(s"_receiver$i", fa.rcv.typ)()
        val tgtDecl = LocalVarDecl(s"_target$i", fa.typ)()
        // From the example translation above for the first target the values are:
        // rcvUse: `_receiver0`
        val rcvUse = LocalVar(rcvDecl.name, rcvDecl.typ)(fa.rcv.pos)
        // rcvInit: `_receiver0 := exprA`
        val rcvInit = LocalVarAssign(rcvUse, fa.rcv)(fa.rcv.pos)
        // --- After the call ---
        // tgtUse: `_target0`
        val tgtUse = LocalVar(tgtDecl.name, tgtDecl.typ)(fa.pos)
        // rcvFa: `_receiver0.f`
        val rcvFa = FieldAccess(rcvUse, fa.field)(fa.pos, fa.info, NodeTrafo(fa) + fa.errT)
        // faAssign: `_receiver0.f := _target0`
        val faAssign = FieldAssign(rcvFa, tgtUse)(rcvFa.pos)
        (Some((rcvDecl, tgtDecl, rcvInit, faAssign)), tgtUse)
      }
      case _ => sys.error(s"Found invalid target of assignment")
    }
    val assn = assign(ts.map(_._2))
    val tmps = ts.flatMap(_._1)
    if (tmps.isEmpty)
      return assn
    if (!Consistency.noDuplicates(tmps.map(_._4.lhs.field)))
      Consistency.messages ++= FastMessaging.message(errorNode, s"multiple targets which access the same field are not allowed")
    Seqn(
      tmps.map(_._3) ++
      Seq(assn) ++
      tmps.map(_._4),
      tmps.flatMap(t => Seq(t._1, t._2))
    )(assn.pos, assn.info)
  }

  /** Helper function that translates subexpressions common to a Havoc or Havocall statement */
  def havocStmtHelper(lhs: Option[(PExp, _)], e: PExp): (Option[Exp], ResourceAccess) = {
    val newLhs = lhs.map(lhs => exp(lhs._1))
    exp(e) match {
      case exp: FieldAccess => (newLhs, exp)
      case PredicateAccessPredicate(predAccess, perm) =>
        // A PrediateAccessPredicate is a PredicateResourceAccess combined with
        // a Permission. Havoc expects a ResourceAccess. To make types match,
        // we must extract the PredicateResourceAccess.
        assert(perm.isEmpty || perm.get.isInstanceOf[FullPerm])
        (newLhs, predAccess)
      case exp: MagicWand => (newLhs, exp)
      case _ => sys.error("Can't havoc this kind of expression")
    }
  }

  def extractAnnotation(pexp: PExp): (PExp, Map[String, Seq[String]]) = {
    pexp match {
      case PAnnotatedExp(ann, e) =>
        val (resPexp, innerMap) = extractAnnotation(e)
        val combinedValue = if (innerMap.contains(ann.key.str)) {
          ann.values.inner.toSeq.map(_.str) ++ innerMap(ann.key.str)
        } else {
          ann.values.inner.toSeq.map(_.str)
        }
        (resPexp, innerMap.updated(ann.key.str, combinedValue))
      case _ => (pexp, Map())
    }
  }

  def extractAnnotationFromStmt(pStmt: PStmt): (PStmt, Map[String, Seq[String]]) = {
    pStmt match {
      case PAnnotatedStmt(ann, s) =>
        val (resPStmt, innerMap) = extractAnnotationFromStmt(s)
        val combinedValue = if (innerMap.contains(ann.key.str)) {
          ann.values.inner.toSeq.map(_.str) ++ innerMap(ann.key.str)
        } else {
          ann.values.inner.toSeq.map(_.str)
        }
        (resPStmt, innerMap.updated(ann.key.str, combinedValue))
      case _ => (pStmt, Map())
    }
  }

  def exp(parseExp: PExp): Exp = exp(parseExp, None)

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(parseExp: PExp, dependencyType: Option[DependencyType]): Exp = {
    val pos = parseExp
    val (pexp, annotationMap) = extractAnnotation(parseExp)
    val sourcePNodeInfo = SourcePNodeInfo(parseExp)
    val info0 = if (annotationMap.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotationMap))
    val info = if(dependencyType.isDefined) MakeInfoPair(info0, DependencyTypeInfo(dependencyType.get)) else info0
    expInternal(pexp, pos, info, dependencyType)
  }

  protected def expInternal(pexp: PExp, pos: PExp, info: Info, dependencyType: Option[DependencyType]): Exp = {

    def goExp(parseExp: PExp) = exp(parseExp, dependencyType)

    def attachMeta(createExp: (Position, Info, ErrorTrafo) => Exp, _pos: PExp = pos, _info: Info = info, _errT: ErrorTrafo = NoTrafos): Exp = {
      val finalInfo = MakeInfoPair(AnalysisSourceInfo.createAnalysisSourceInfo(createExp(_pos, _info, _errT)), _info)
      createExp(_pos, finalInfo, _errT)
    }

    pexp match {
      case PIdnUseExp(piu) =>
        piu.decl match {
          case Some(_: PTypedVarDecl) => attachMeta(LocalVar(piu.name, ttyp(pexp.typ)))
          // A malformed AST where a field, function or other declaration is used as a variable.
          // Should have been caught by the type checker.
          case _ => sys.error("should not occur in type-checked program")
        }
      case pbe @ PBinExp(left, op, right) =>
        val (l, r) = (goExp(left), goExp(right))
        op.rs match {
          case PSymOp.Plus =>
            r.typ match {
              case Int => attachMeta(Add(l, r))
              case Perm => attachMeta(PermAdd(l, r))
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Minus =>
            r.typ match {
              case Int => attachMeta(Sub(l, r))
              case Perm => attachMeta(PermSub(l, r))
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Mul =>
            r.typ match {
              case Int =>
                l.typ match {
                  case Int => attachMeta(Mul(l, r))
                  case Perm => attachMeta(IntPermMul(r, l))
                  case _ => sys.error("should not occur in type-checked program")
                }
              case Perm =>
                l.typ match {
                  case Int => attachMeta(IntPermMul(l, r))
                  case Perm => attachMeta(PermMul(l, r))
                  case _ => sys.error("should not occur in type-checked program")
                }
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Div =>
            l.typ match {
              case Perm => r.typ match {
                case Int => attachMeta(PermDiv(l, r))
                case Perm => attachMeta(PermPermDiv(l, r))
              }
              case Int  =>
                assert (r.typ==Int)
                if (ttyp(pbe.typ) == Int)
                  attachMeta(Div(l, r))
                else
                  attachMeta(FractionalPerm(l, r))
              case _    => sys.error("should not occur in type-checked program")
            }
          case PSymOp.ArithDiv => attachMeta(Div(l, r))
          case PSymOp.Mod => attachMeta(Mod(l, r))
          case PSymOp.Lt =>
            l.typ match {
              case Int => attachMeta(LtCmp(l, r))
              case Perm => attachMeta(PermLtCmp(l, r))
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Le =>
            l.typ match {
              case Int => attachMeta(LeCmp(l, r))
              case Perm => attachMeta(PermLeCmp(l, r))
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Gt =>
            l.typ match {
              case Int => attachMeta(GtCmp(l, r))
              case Perm => attachMeta(PermGtCmp(l, r))
              case _ => sys.error("unexpected type " + l.typ.toString())
            }
          case PSymOp.Ge =>
            l.typ match {
              case Int => attachMeta(GeCmp(l, r))
              case Perm => attachMeta(PermGeCmp(l, r))
              case _ => sys.error("unexpected type")
            }
          case PSymOp.EqEq => attachMeta(EqCmp(l, r))
          case PSymOp.Ne => attachMeta(NeCmp(l, r))
          case PSymOp.Implies => attachMeta(Implies(l, r))
          case PSymOp.Wand => attachMeta(MagicWand(l, r))
          case PSymOp.Iff => attachMeta(EqCmp(l, r))
          case PSymOp.AndAnd => attachMeta(And(l, r))
          case PSymOp.OrOr => attachMeta(Or(l, r))

          case PKwOp.In => right.typ match {
            case _: PSeqType => attachMeta(SeqContains(l, r))
            case _: PMapType => attachMeta(MapContains(l, r))
            case _: PSetType | _: PMultisetType => attachMeta(AnySetContains(l, r))
            case t => sys.error(s"unexpected type $t")
          }

          case PSymOp.Append => attachMeta(SeqAppend(l, r))
          case PKwOp.Subset => attachMeta(AnySetSubset(l, r))
          case PKwOp.Intersection => attachMeta(AnySetIntersection(l, r))
          case PKwOp.Union => attachMeta(AnySetUnion(l, r))
          case PKwOp.Setminus => attachMeta(AnySetMinus(l, r))
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = goExp(pe)
        op.rs match {
          case PSymOp.Neg =>
            e.typ match {
              case Int => attachMeta(Minus(e))
              case Perm => attachMeta(PermMinus(e))
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Not => attachMeta(Not(e))
        }
      case PInhaleExhaleExp(_, in, _, ex, _) =>
        attachMeta(InhaleExhaleExp(goExp(in), goExp(ex)))
      case PIntLit(i) =>
        attachMeta(IntLit(i))
      case p@PResultLit(_) =>
        // find function
        val func = p.getAncestor[PFunction].get
        attachMeta(Result(ttyp(func.typ.resultType)))
      case bool: PBoolLit =>
        if (bool.b) attachMeta(TrueLit()) else attachMeta(FalseLit())
      case PNullLit(_) =>
        attachMeta(NullLit())
      case PFieldAccess(rcv, _, idn) =>
        attachMeta(FieldAccess(goExp(rcv), findField(idn)))
      case PMagicWandExp(left, _, right) => attachMeta(MagicWand(goExp(left), goExp(right)))
      case pfa@PCall(func, args, _) =>
        members(func.name) match {
          case f: Function => attachMeta(FuncApp(f, args.inner.toSeq map goExp))
          case f @ DomainFunc(_, _, _, _, _) =>
            val actualArgs = args.inner.toSeq map goExp
            /* TODO: Not used - problem?*/
            type TypeSubstitution = Map[TypeVar, Type]
            val so : Option[TypeSubstitution] = pfa.domainSubstitution match{
              case Some(ps) => Some(ps.m.map(kv=>TypeVar(kv._1)->ttyp(kv._2)))
              case None => None
            }
            so match {
              case Some(s) =>
                val d = members(f.domainName).asInstanceOf[Domain]
                assert(s.keys.toSet.subsetOf(d.typVars.toSet))
                val sp = s //completeWithDefault(d.typVars,s)
                assert(sp.keys.toSet == d.typVars.toSet)
                if (f.interpretation.isDefined)
                  attachMeta(BackendFuncApp(f, actualArgs))
                else
                  attachMeta(DomainFuncApp(f, actualArgs, sp))
              case _ => sys.error("type unification error - should report and not crash")
            }
          case _: Predicate =>
            val inner = PredicateAccess(args.inner.toSeq map goExp, findPredicate(func).name)(pos, info)
            attachMeta(PredicateAccessPredicate(inner, None))
          case _ => sys.error("unexpected reference to non-function")
        }
      case PNewExp(_, _) => sys.error("unexpected `new` expression")
      case PUnfolding(_, loc, _, e) =>
        attachMeta(Unfolding(goExp(loc).asInstanceOf[PredicateAccessPredicate], goExp(e)))
      case PApplying(_, wand, _, e) =>
        attachMeta(Applying(goExp(wand).asInstanceOf[MagicWand], goExp(e)))
      case PAsserting(_, a, _, e) =>
        attachMeta(Asserting(goExp(a), goExp(e)))
      case pl@PLet(_, _, _, exp1, _, PLetNestedScope(body)) =>
        attachMeta(Let(liftLogicalDecl(pl.decl), goExp(exp1.inner), goExp(body)))
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(_, vars, _, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp.inner.toSeq map goExp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        attachMeta(Exists(vars.toSeq map liftLogicalDecl, ts, goExp(e)))
      case PForall(_, vars, _, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp.inner.toSeq map goExp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        val fa = attachMeta(Forall(vars.toSeq map liftLogicalDecl, ts, goExp(e)))
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa.asInstanceOf[Forall])
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      case fp@PForPerm(_, vars, _, _, e) =>
        val varList = vars.toSeq map liftLogicalDecl
        goExp(fp.accessRes) match {
          case PredicateAccessPredicate(inner, _) => attachMeta(ForPerm(varList, inner, goExp(e)))
          case f : FieldAccess => attachMeta(ForPerm(varList, f, goExp(e)))
          case p : PredicateAccess => attachMeta(ForPerm(varList, p, goExp(e)))
          case w : MagicWand => attachMeta(ForPerm(varList, w, goExp(e)))
          case other =>
            sys.error(s"Internal Error: Unexpectedly found $other in forperm")
        }
      case POldExp(_, lbl, e) =>
        val ee = goExp(e.inner)
        lbl.map(l => attachMeta(LabelledOld(ee, l.inner.fold(i => i.rs.keyword, i1 => i1.name)))).getOrElse(attachMeta(Old(ee)))
      case PCondExp(cond, _, thn, _, els) =>
        attachMeta(CondExp(goExp(cond), goExp(thn), goExp(els)))
      case PCurPerm(_, res) =>
        goExp(res.inner) match {
          case PredicateAccessPredicate(inner, _) => attachMeta(CurrentPerm(inner))
          case x: FieldAccess => attachMeta(CurrentPerm(x))
          case x: PredicateAccess => attachMeta(CurrentPerm(x))
          case x: MagicWand => attachMeta(CurrentPerm(x))
          case other => sys.error(s"Unexpectedly found $other")
        }
      case PNoPerm(_) =>
        attachMeta(NoPerm())
      case PFullPerm(_) =>
        attachMeta(FullPerm())
      case PWildcard(_) =>
        attachMeta(WildcardPerm())
      case PEpsilon(_) =>
        attachMeta(EpsilonPerm())
      case acc: PAccPred =>
        val p = acc.permExp.map(goExp)
        goExp(acc.loc) match {
          case loc@FieldAccess(_, _) =>
            attachMeta(FieldAccessPredicate(loc, p))
          case loc@PredicateAccess(_, _) =>
            attachMeta(PredicateAccessPredicate(loc, p))
          case PredicateAccessPredicate(inner, _) => attachMeta(PredicateAccessPredicate(inner, p))
          case _ =>
            sys.error("unexpected location")
        }
      case _: PEmptySeq =>
        attachMeta(EmptySeq(ttyp(pexp.typ.asInstanceOf[PSeqType].elementType.inner)))
      case PExplicitSeq(_, elems) =>
        attachMeta(ExplicitSeq(elems.inner.toSeq map goExp))
      case PRangeSeq(_, low, _, high, _) =>
        attachMeta(RangeSeq(goExp(low), goExp(high)))

      case PLookup(base, _, index, _) => base.typ match {
        case _: PSeqType => attachMeta(SeqIndex(goExp(base), goExp(index)))
        case _: PMapType => attachMeta(MapLookup(goExp(base), goExp(index)))
        case t => sys.error(s"unexpected type $t")
      }

      case PSeqSlice(seq, _, s, _, e, _) =>
        val es = goExp(seq)
        val ss = e.map(goExp).map(e1 => attachMeta(SeqTake(es, e1))).getOrElse(es)
        s.map(goExp).map(e1 => attachMeta(SeqDrop(ss, e1))).getOrElse(ss)

      case PUpdate(base, _, key, _, value, _) => base.typ match {
        case _: PSeqType => attachMeta(SeqUpdate(goExp(base), goExp(key), goExp(value)))
        case _: PMapType => attachMeta(MapUpdate(goExp(base), goExp(key), goExp(value)))
        case t => sys.error(s"unexpected type $t")
      }

      case PSize(_, base, _) => base.typ match {
        case _: PSeqType => attachMeta(SeqLength(goExp(base)))
        case _: PMapType => attachMeta(MapCardinality(goExp(base)))
        case _: PSetType | _: PMultisetType => attachMeta(AnySetCardinality(goExp(base)))
        case t => sys.error(s"unexpected type $t")
      }

      case _: PEmptySet =>
        attachMeta(EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType.inner)))
      case PExplicitSet(_, elems) =>
        attachMeta(ExplicitSet(elems.inner.toSeq map goExp))
      case _: PEmptyMultiset =>
        attachMeta(EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType.inner)))
      case PExplicitMultiset(_, elems) =>
        attachMeta(ExplicitMultiset(elems.inner.toSeq map goExp))

      case _: PEmptyMap => attachMeta(EmptyMap(
        ttyp(pexp.typ.asInstanceOf[PMapType].keyType),
        ttyp(pexp.typ.asInstanceOf[PMapType].valueType)
      ))
      case PExplicitMap(_, elems) =>
        attachMeta(ExplicitMap(elems.inner.toSeq map goExp))
      case PMaplet(key, _, value) =>
        attachMeta(Maplet(goExp(key), goExp(value)))
      case PMapDomain(_, base) =>
        attachMeta(MapDomain(goExp(base.inner)))
      case PMapRange(_, base) =>
        attachMeta(MapRange(goExp(base.inner)))

      case t: PExtender =>
        val exp = t.translateExp(this)
        exp.withMeta((exp.pos, MakeInfoPair(AnalysisSourceInfo.createAnalysisSourceInfo(exp), exp.info), exp.errT))
    }
  }

  implicit def liftPos(node: Where): SourcePosition = Translator.liftWhere(node)

  /** Takes a `PAnyFormalArgDecl` and turns it into a `AnyLocalVarDecl`. */
  def liftAnyArgDecl(formal: PAnyFormalArgDecl) =
    formal match {
      case f: PFormalArgDecl => liftArgDecl(f)
      case PDomainFunctionArg(Some(idndef), _, typ) => LocalVarDecl(idndef.name, ttyp(typ))(idndef)
      case PDomainFunctionArg(None, _, typ) => UnnamedLocalVarDecl(ttyp(typ))(typ)
    }

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVarDecl`. */
  def liftArgDecl(formal: PFormalArgDecl) =
      LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(pos = formal.idndef, info = SourcePNodeInfo(formal))

  /** Takes a `PFormalReturnDecl` and turns it into a `LocalVarDecl`. */
  def liftReturnDecl(formal: PFormalReturnDecl) =
      LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(pos = formal.idndef, info = SourcePNodeInfo(formal))

  /** Takes a `PLogicalVarDecl` and turns it into a `LocalVarDecl`. */
  def liftLogicalDecl(logical: PLogicalVarDecl) =
      LocalVarDecl(logical.idndef.name, ttyp(logical.typ))(pos = logical.idndef, info = SourcePNodeInfo(logical))

  /** Takes a `PType` and turns it into a `Type`. */
  def ttyp(t: PType): Type = t match {
    case PPrimitiv(name) => name.rs match {
      case PKw.Int => Int
      case PKw.Bool => Bool
      case PKw.Ref => Ref
      case PKw.Perm => Perm
      case PKw.Rational => Perm
    }
    case PSeqType(_, elemType) =>
      SeqType(ttyp(elemType.inner))
    case PSetType(_, elemType) =>
      SetType(ttyp(elemType.inner))
    case PMultisetType(_, elemType) =>
      MultisetType(ttyp(elemType.inner))
    case typ: PMapType =>
      MapType(ttyp(typ.keyType), ttyp(typ.valueType))
    case typ@PDomainType(name, _) =>
      members.get(name.name) match {
        case Some(domain: Domain) =>
          if (domain.interpretations.isDefined) {
            BackendType(domain.name, domain.interpretations.get)
          } else {
            val typVarMapping = domain.typVars zip (typ.typeArgs map ttyp)
            DomainType(domain, typVarMapping /*.filter {
            case (tv, tt) => tv!=tt //!tt.isInstanceOf[TypeVar]
          }*/.toMap)
          }
        case Some(adt: Adt) =>
          val typVarMapping = adt.typVars zip (typ.typeArgs map ttyp)
          AdtType(adt, typVarMapping.toMap)
        case Some(other) =>
          sys.error(s"Did not expect member ${other}")
        case None =>
          assert(typ.typeArgs.isEmpty)
          TypeVar(name.name) // not a domain, i.e. it must be a type variable
      }
    case TypeHelper.Wand => Wand
    case TypeHelper.Predicate => Bool
    case TypeHelper.Impure => Bool
    case t: PExtender => t.translateType(this)
    case PUnknown() =>
      sys.error("unknown type unexpected here")
    case _: PFunctionType =>
      sys.error("unexpected use of internal typ")
  }
}

object Translator {
  import scala.annotation.unused

  /** Takes a [[viper.silver.parser.FastPositioned]] and turns it into a [[viper.silver.ast.SourcePosition]]. */
  implicit def liftWhere(node: Where): SourcePosition = {
    if (node.pos._1.isInstanceOf[FilePosition]) {
      assert(node.pos._2.isInstanceOf[FilePosition])

      val begin = node.pos._1.asInstanceOf[FilePosition]
      val end = node.pos._2.asInstanceOf[FilePosition]

      SourcePosition(begin.file,
        LineColumnPosition(begin.line, begin.column),
        LineColumnPosition(end.line, end.column))
    }
    else {
      SourcePosition(null, 0, 0)
    }
  }

  def toInfo(annotations: Seq[PAnnotation], @unused node: PNode): Info = {
    if (annotations.isEmpty) {
      NoInfo
    } else {
      AnnotationInfo(annotations.groupBy(_.key).map{ case (k, v) => k.str -> v.flatMap(_.values.inner.toSeq.map(_.str)) })
    }
  }
}
