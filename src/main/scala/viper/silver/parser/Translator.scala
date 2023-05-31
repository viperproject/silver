// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.FastMessaging
import viper.silver.ast.utility._
import viper.silver.ast.{SourcePosition, _}
import viper.silver.plugin.standard.adt.{Adt, AdtType}

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

    program match {
      case PProgram(_, _, pdomains, pfields, pfunctions, ppredicates, pmethods, pextensions, _) =>

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
        pdomains flatMap (_.members.funcs) foreach translateMemberSignature
        (pfields ++ pfunctions ++ ppredicates ++ pmethods) foreach translateMemberSignature

        /* [2022-03-14 Alessandro] After the signatures are translated, the actual full translations can be done
         * independently of each other.
         */
        val extensions = pextensions map translate
        val domain = (pdomains map translate) ++ extensions filter (t => t.isInstanceOf[Domain])
        val fields = (pfields map translate) ++ extensions filter (t => t.isInstanceOf[Field])
        val functions = (pfunctions map translate) ++ extensions filter (t => t.isInstanceOf[Function])
        val predicates = (ppredicates map translate) ++ extensions filter (t => t.isInstanceOf[Predicate])
        val methods = (pmethods map translate)  ++ extensions filter (t => t.isInstanceOf[Method])



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
  }

  private def translate(t: PExtender): Member = {
    t.translateMember(this)
  }

  private def translate(m: PMethod): Method = m match {
    case PMethod(_, _, name, _, _, pres, posts, body) =>
      val m = findMethod(name)

      val newBody = body.map(actualBody => {
        val b = stmt(actualBody).asInstanceOf[Seqn]
        val newScopedDecls = b.scopedSeqnDeclarations ++ b.deepCollect {case l: Label => l}

        b.copy(scopedSeqnDeclarations = newScopedDecls)(b.pos, b.info, b.errT)
      })

      val finalMethod = m.copy(pres = pres map (p => exp(p._2)), posts = posts map (p => exp(p._2)), body = newBody)(m.pos, m.info, m.errT)

      members(m.name) = finalMethod

      finalMethod
  }

  private def translate(d: PDomain): Domain = d match {
    case PDomain(_, _, name, _, PDomainMembers(functions, axioms), interpretation) =>
      val d = findDomain(name)
      val dd = d.copy(functions = functions map (f => findDomainFunction(f.idndef)),
        axioms = axioms map translate, interpretations = interpretation)(d.pos, d.info, d.errT)
      members(d.name) = dd
      dd
  }

  private def translate(a: PAxiom): DomainAxiom = a match {
    case pa@PAxiom(anns, _, Some(name), e) =>
      NamedDomainAxiom(name.name, exp(e.inner))(a, Translator.toInfo(anns, pa), domainName = pa.domainName.name)
    case pa@PAxiom(anns, _, None, e) =>
      AnonymousDomainAxiom(exp(e.inner))(a, Translator.toInfo(anns, pa), domainName = pa.domainName.name)
  }

  private def translate(f: PFunction): Function = f match {
    case PFunction(_, _, name, _, _, pres, posts, body) =>
      val f = findFunction(name)
      val ff = f.copy( pres = pres map (p => exp(p._2)), posts = posts map (p => exp(p._2)), body = body map (_.inner) map exp)(f.pos, f.info, f.errT)
      members(f.name) = ff
      ff
  }

  private def translate(p: PPredicate): Predicate = p match {
    case PPredicate(_, _, name, _, body) =>
      val p = findPredicate(name)
      val pp = p.copy(body = body map (_.inner) map exp)(p.pos, p.info, p.errT)
      members(p.name) = pp
      pp
  }

  private def translate(f: PField) = findField(f.idndef)

  private val members = collection.mutable.HashMap[String, Node]()
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
  private def translateMemberSignature(p: PMember): Unit = {
    val pos = p
    val name = p.idndef.name
    val t = p match {
      case pf@PField(anns, _, _, typ) =>
        Field(name, ttyp(typ))(pos, Translator.toInfo(anns, pf))
      case pf@PFunction(anns, _, _, formalArgs, typ, _, _, _) =>
        Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null)(pos, Translator.toInfo(anns, pf))
      case pdf@ PDomainFunction(anns, _, _, args, typ, unique, interp) =>
        DomainFunc(name, args map liftAnyVarDecl, ttyp(typ), unique, interp)(pos,Translator.toInfo(anns, pdf),pdf.domainName.name)
      case pd@PDomain(anns, _, _, typVars, _, interp) =>
        Domain(name, null, null, typVars map (t => TypeVar(t.idndef.name)), interp)(pos, Translator.toInfo(anns, pd))
      case pp@PPredicate(anns, _, _, formalArgs, _) =>
        Predicate(name, formalArgs map liftVarDecl, null)(pos, Translator.toInfo(anns, pp))
      case pm@PMethod(anns, _, _, formalArgs, formalReturns, _, _, _) =>
        Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null)(pos, Translator.toInfo(anns, pm))
    }
    members.put(p.idndef.name, t)
  }

  private def translateMemberSignature(p: PExtender): Unit ={
    p match {
      case t: PMember =>
        val l = p.translateMemberSignature(this)
        members.put(t.idndef.name, l)
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
    val info = if (annotations.isEmpty) NoInfo else AnnotationInfo(annotations)
    val subInfo = NoInfo
    s match {
      case p@PVarAssign(idnuse, PCall(func, args, _)) if members(func.name).isInstanceOf[Method] =>
        /* This is a method call that got parsed in a slightly confusing way.
         * TODO: Get rid of this case! There is a matching case in the resolver.
         */
        val call = PMethodCall(Seq(idnuse), func, args)(p.pos)
        val res = stmt(call)
        res.withMeta(res.pos, info, res.errT)
      case PVarAssign(idnuse, rhs) =>
        LocalVarAssign(LocalVar(idnuse.name, ttyp(idnuse.typ))(pos, subInfo), exp(rhs))(pos, info)
      case PFieldAssign(field, rhs) =>
        FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnuse))(field), exp(rhs))(pos, info)
      case PLocalVarDecl(_, idndef, t, Some(init)) =>
        LocalVarAssign(LocalVar(idndef.name, ttyp(t))(pos, subInfo), exp(init))(pos, info)
      case PLocalVarDecl(_, _, _, None) =>
        // there are no declarations in the Viper AST; rather they are part of the scope signature
        Statements.EmptyStmt
      case PSeqn(ss) =>
        val plocals = ss.collect {
          case l: PLocalVarDecl => Some(l)
          case _ => None
        }
        val locals = plocals.flatten.map {
          case p@PLocalVarDecl(_, idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(p)
        }
        Seqn(ss filterNot (_.isInstanceOf[PSkip]) map stmt, locals)(pos, info)
      case PFold(_, e) =>
        Fold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, info)
      case PUnfold(_, e) =>
        Unfold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, info)
      case PPackageWand(_, e, proofScript) =>
        val wand = exp(e).asInstanceOf[MagicWand]
        Package(wand, stmt(proofScript).asInstanceOf[Seqn])(pos, info)
      case PApplyWand(_, e) =>
        Apply(exp(e).asInstanceOf[MagicWand])(pos, info)
      case PInhale(_, e) =>
        Inhale(exp(e))(pos, info)
      case PAssume(_, e) =>
        Assume(exp(e))(pos, info)
      case PExhale(_, e) =>
        Exhale(exp(e))(pos, info)
      case PAssert(_, e) =>
        Assert(exp(e))(pos, info)
      case PNewStmt(target, fieldsOpt) =>
        val fields = fieldsOpt match {
          case None => program.fields map translate
            /* Slightly redundant since we already translated the fields when we
             * translated the PProgram at the beginning of this class.
             */
          case Some(pfields) => pfields map findField
        }
        NewStmt(exp(target).asInstanceOf[LocalVar], fields)(pos, info)
      case PMethodCall(targets, method, args) =>
        val ts = (targets map exp).asInstanceOf[Seq[LocalVar]]
        MethodCall(findMethod(method), args map exp, ts)(pos, info)
      case PLabel(_, name, invs) =>
        Label(name.name, invs map (inv => exp(inv._2)))(pos, info)
      case PGoto(_, label) =>
        Goto(label.name)(pos, info)
      case PIf(_, cond, thn, _, els) =>
        If(exp(cond), stmt(thn).asInstanceOf[Seqn], stmt(els).asInstanceOf[Seqn])(pos, info)
      case PWhile(_, cond, invs, body) =>
        While(exp(cond), invs map (inv => exp(inv._2)), stmt(body).asInstanceOf[Seqn])(pos, info)
      case PQuasihavoc(_, lhs, e) =>
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavoc(newLhs, newE)(pos, info)
      case PQuasihavocall(_, vars, _, lhs, e) =>
        val newVars = vars map liftVarDecl
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavocall(newVars, newLhs, newE)(pos, info)
      case t: PExtender =>   t.translateStmt(this)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }
  }

  /** Helper function that translates subexpressions common to a Havoc or Havocall statement */
  def havocStmtHelper(lhs: Option[(PExp, POperator)], e: PExp): (Option[Exp], ResourceAccess) = {
    val newLhs = lhs.map(lhs => exp(lhs._1))
    exp(e) match {
      case exp: FieldAccess => (newLhs, exp)
      case PredicateAccessPredicate(predAccess, perm) =>
        // A PrediateAccessPredicate is a PredicateResourceAccess combined with
        // a Permission. Havoc expects a ResourceAccess. To make types match,
        // we must extract the PredicateResourceAccess.
        assert(perm.isInstanceOf[FullPerm])
        (newLhs, predAccess)
      case exp: MagicWand => (newLhs, exp)
      case _ => sys.error("Can't havoc this kind of expression")
    }
  }

  def extractAnnotation(pexp: PExp): (PExp, Map[String, Seq[String]]) = {
    pexp match {
      case PAnnotatedExp(e, ann) =>
        val (resPexp, innerMap) = extractAnnotation(e)
        val combinedValue = if (innerMap.contains(ann.key)) {
          ann.values ++ innerMap(ann.key)
        } else {
          ann.values
        }
        (resPexp, innerMap.updated(ann.key, combinedValue))
      case _ => (pexp, Map())
    }
  }

  def extractAnnotationFromStmt(pStmt: PStmt): (PStmt, Map[String, Seq[String]]) = {
    pStmt match {
      case PAnnotatedStmt(s, ann) =>
        val (resPStmt, innerMap) = extractAnnotationFromStmt(s)
        val combinedValue = if (innerMap.contains(ann.key)) {
          ann.values ++ innerMap(ann.key)
        } else {
          ann.values
        }
        (resPStmt, innerMap.updated(ann.key, combinedValue))
      case _ => (pStmt, Map())
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(parseExp: PExp): Exp = {
    val pos = parseExp
    val (pexp, annotationMap) = extractAnnotation(parseExp)
    val info = if (annotationMap.isEmpty) NoInfo else AnnotationInfo(annotationMap)
    pexp match {
      case piu @ PIdnUse(name) =>
        piu.decl match {
          case _: PLocalVarDecl | _: PFormalArgDecl => LocalVar(name, ttyp(pexp.typ))(pos, info)
          case pf: PField =>
            /* A malformed AST where a field is dereferenced without a receiver */
            Consistency.messages ++= FastMessaging.message(piu, s"expected expression but found field $name")
            LocalVar(pf.idndef.name, ttyp(pf.typ))(pos, info)
          case _ =>
            sys.error("should not occur in type-checked program")
        }
      case pbe @ PBinExp(left, op, right) =>
        val (l, r) = (exp(left), exp(right))
        op.operator match {
          case "+" =>
            r.typ match {
              case Int => Add(l, r)(pos, info)
              case Perm => PermAdd(l, r)(pos, info)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "-" =>
            r.typ match {
              case Int => Sub(l, r)(pos, info)
              case Perm => PermSub(l, r)(pos, info)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "*" =>
            r.typ match {
              case Int =>
                l.typ match {
                  case Int => Mul(l, r)(pos, info)
                  case Perm => IntPermMul(r, l)(pos, info)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case Perm =>
                l.typ match {
                  case Int => IntPermMul(l, r)(pos, info)
                  case Perm => PermMul(l, r)(pos, info)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case _ => sys.error("should not occur in type-checked program")
            }
          case "/" =>
            l.typ match {
              case Perm => r.typ match {
                case Int => PermDiv(l, r)(pos, info)
                case Perm => PermPermDiv(l, r)(pos, info)
              }
              case Int  =>
                assert (r.typ==Int)
                if (ttyp(pbe.typ) == Int)
                  Div(l, r)(pos, info)
                else
                  FractionalPerm(l, r)(pos, info)
              case _    => sys.error("should not occur in type-checked program")
            }
          case "\\" => Div(l, r)(pos, info)
          case "%" => Mod(l, r)(pos, info)
          case "<" =>
            l.typ match {
              case Int => LtCmp(l, r)(pos, info)
              case Perm => PermLtCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case "<=" =>
            l.typ match {
              case Int => LeCmp(l, r)(pos, info)
              case Perm => PermLeCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case ">" =>
            l.typ match {
              case Int => GtCmp(l, r)(pos, info)
              case Perm => PermGtCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case ">=" =>
            l.typ match {
              case Int => GeCmp(l, r)(pos, info)
              case Perm => PermGeCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case "==" => EqCmp(l, r)(pos, info)
          case "!=" => NeCmp(l, r)(pos, info)
          case "==>" => Implies(l, r)(pos, info)
          case "--*" => MagicWand(l, r)(pos, info)
          case "<==>" => EqCmp(l, r)(pos, info)
          case "&&" => And(l, r)(pos, info)
          case "||" => Or(l, r)(pos, info)

          case "in" => right.typ match {
            case _: PSeqType => SeqContains(l, r)(pos, info)
            case _: PMapType => MapContains(l, r)(pos, info)
            case _: PSetType | _: PMultisetType => AnySetContains(l, r)(pos, info)
            case t => sys.error(s"unexpected type $t")
          }

          case "++" => SeqAppend(l, r)(pos, info)
          case "subset" => AnySetSubset(l, r)(pos, info)
          case "intersection" => AnySetIntersection(l, r)(pos, info)
          case "union" => AnySetUnion(l, r)(pos, info)
          case "setminus" => AnySetMinus(l, r)(pos, info)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op.operator match {
          case "-" =>
            e.typ match {
              case Int => Minus(e)(pos, info)
              case Perm => PermMinus(e)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case "!" => Not(e)(pos, info)
        }
      case PInhaleExhaleExp(in, ex) =>
        InhaleExhaleExp(exp(in), exp(ex))(pos, info)
      case PIntLit(i) =>
        IntLit(i)(pos, info)
      case p@PResultLit(_) =>
        // find function
        var par: PNode = p.parent.get
        while (!par.isInstanceOf[PFunction]) {
          if (par == null) sys.error("cannot use 'result' outside of function")
          par = par.parent.get
        }
        Result(ttyp(par.asInstanceOf[PFunction].typ))(pos, info)
      case PBoolLit(_, b) =>
        if (b) TrueLit()(pos, info) else FalseLit()(pos, info)
      case PNullLit(_) =>
        NullLit()(pos, info)
      case PFieldAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos, info)
      // case PPredicateAccess(args, idn) =>
      //   PredicateAccess(args map exp, findPredicate(idn).name)(pos, info)
      case PMagicWandExp(left, _, right) => MagicWand(exp(left), exp(right))(pos, info)
      case pfa@PCall(func, args, _) =>
        members(func.name) match {
          case f: Function => FuncApp(f, args map exp)(pos, info)
          case f @ DomainFunc(_, _, _, _, _) =>
            val actualArgs = args map exp
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
                  BackendFuncApp(f, actualArgs)(pos, info)
                else
                  DomainFuncApp(f, actualArgs, sp)(pos, info)
              case _ => sys.error("type unification error - should report and not crash")
            }
          case _: Predicate =>
            val inner = PredicateAccess(args map exp, findPredicate(func).name) (pos, info)
            val fullPerm = FullPerm()(pos, info)
            PredicateAccessPredicate(inner, fullPerm) (pos, info)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PUnfolding(_, loc, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos, info)
      case PApplying(_, wand, e) =>
        Applying(exp(wand).asInstanceOf[MagicWand], exp(e))(pos, info)
      case PLet(exp1, PLetNestedScope(variable, body)) =>
        Let(liftVarDecl(variable), exp(exp1), exp(body))(pos, info)
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(_, vars, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        Exists(vars map liftVarDecl, ts, exp(e))(pos, info)
      case PForall(_, vars, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        val fa = Forall(vars map liftVarDecl, ts, exp(e))(pos, info)
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      case PForPerm(_, vars, res, e) =>
        val varList = vars map liftVarDecl
        exp(res) match {
          case PredicateAccessPredicate(inner, _) => ForPerm(varList, inner, exp(e))(pos, info)
          case f : FieldAccess => ForPerm(varList, f, exp(e))(pos, info)
          case p : PredicateAccess => ForPerm(varList, p, exp(e))(pos, info)
          case w : MagicWand => ForPerm(varList, w, exp(e))(pos, info)
          case other =>
            sys.error(s"Internal Error: Unexpectedly found $other in forperm")
        }
      case POld(e) =>
        Old(exp(e))(pos, info)
      case PLabelledOld(lbl,e) =>
        LabelledOld(exp(e),lbl.name)(pos, info)
      case PCondExp(cond, _, thn, _, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos, info)
      case PCurPerm(res) =>
        exp(res) match {
          case PredicateAccessPredicate(inner, _) => CurrentPerm(inner)(pos, info)
          case x: FieldAccess => CurrentPerm(x)(pos, info)
          case x: PredicateAccess => CurrentPerm(x)(pos, info)
          case x: MagicWand => CurrentPerm(x)(pos, info)
          case other => sys.error(s"Unexpectedly found $other")
        }
      case PNoPerm(_) =>
        NoPerm()(pos, info)
      case PFullPerm(_) =>
        FullPerm()(pos, info)
      case PWildcard(_) =>
        WildcardPerm()(pos, info)
      case PEpsilon(_) =>
        EpsilonPerm()(pos, info)
      case PAccPred(_, loc, perm) =>
        val p = exp(perm)
        exp(loc) match {
          case loc@FieldAccess(_, _) =>
            FieldAccessPredicate(loc, p)(pos, info)
          case loc@PredicateAccess(_, _) =>
            PredicateAccessPredicate(loc, p)(pos, info)
          case PredicateAccessPredicate(inner, _) => PredicateAccessPredicate(inner, p)(pos, info)
          case _ =>
            sys.error("unexpected location")
        }
      case PEmptySeq(_) =>
        EmptySeq(ttyp(pexp.typ.asInstanceOf[PSeqType].elementType))(pos, info)
      case PExplicitSeq(elems) =>
        ExplicitSeq(elems map exp)(pos, info)
      case PRangeSeq(low, high) =>
        RangeSeq(exp(low), exp(high))(pos, info)

      case PLookup(base, index) => base.typ match {
        case _: PSeqType => SeqIndex(exp(base), exp(index))(pos, info)
        case _: PMapType => MapLookup(exp(base), exp(index))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case PSeqTake(seq, n) =>
        SeqTake(exp(seq), exp(n))(pos, info)
      case PSeqDrop(seq, n) =>
        SeqDrop(exp(seq), exp(n))(pos, info)

      case PUpdate(base, key, value) => base.typ match {
        case _: PSeqType => SeqUpdate(exp(base), exp(key), exp(value))(pos, info)
        case _: PMapType => MapUpdate(exp(base), exp(key), exp(value))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case PSize(base) => base.typ match {
        case _: PSeqType => SeqLength(exp(base))(pos, info)
        case _: PMapType => MapCardinality(exp(base))(pos, info)
        case _: PSetType | _: PMultisetType => AnySetCardinality(exp(base))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case PEmptySet(_) =>
        EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType))(pos, info)
      case PExplicitSet(elems) =>
        ExplicitSet(elems map exp)(pos, info)
      case PEmptyMultiset(_) =>
        EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType))(pos, info)
      case PExplicitMultiset(elems) =>
        ExplicitMultiset(elems map exp)(pos, info)

      case PEmptyMap(_, _) => EmptyMap(
        ttyp(pexp.typ.asInstanceOf[PMapType].keyType),
        ttyp(pexp.typ.asInstanceOf[PMapType].valueType)
      )(pos, info)
      case PExplicitMap(elems) =>
        ExplicitMap(elems map exp)(pos, info)
      case PMaplet(key, value) =>
        Maplet(exp(key), exp(value))(pos, info)
      case PMapDomain(base) =>
        MapDomain(exp(base))(pos, info)
      case PMapRange(base) =>
        MapRange(exp(base))(pos, info)

      case t: PExtender => t.translateExp(this)
    }
  }

  implicit def liftPos(node: Where): SourcePosition = Translator.liftWhere(node)

  /** Takes a `PAnyFormalArgDecl` and turns it into a `AnyLocalVarDecl`. */
  def liftAnyVarDecl(formal: PAnyFormalArgDecl) =
    formal match {
      case f: PFormalArgDecl => LocalVarDecl(f.idndef.name, ttyp(f.typ))(f.idndef)
      case u: PUnnamedFormalArgDecl => UnnamedLocalVarDecl(ttyp(u.typ))(u.typ)
    }

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVarDecl`. */
  def liftVarDecl(formal: PFormalArgDecl) =
      LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(formal.idndef)

  /** Takes a `PType` and turns it into a `Type`. */
  def ttyp(t: PType): Type = t match {
    case PPrimitiv(PKeywordType(name)) => name match {
      case "Int" => Int
      case "Bool" => Bool
      case "Ref" => Ref
      case "Perm" => Perm
    }
    case PSeqType(_, elemType) =>
      SeqType(ttyp(elemType))
    case PSetType(_, elemType) =>
      SetType(ttyp(elemType))
    case PMultisetType(_, elemType) =>
      MultisetType(ttyp(elemType))
    case PMapType(_, keyType, valueType) =>
      MapType(ttyp(keyType), ttyp(valueType))
    case PDomainType(name, args) =>
      members.get(name.name) match {
        case Some(domain: Domain) =>
          if (domain.interpretations.isDefined) {
            BackendType(domain.name, domain.interpretations.get)
          } else {
            val typVarMapping = domain.typVars zip (args map ttyp)
            DomainType(domain, typVarMapping /*.filter {
            case (tv, tt) => tv!=tt //!tt.isInstanceOf[TypeVar]
          }*/.toMap)
          }
        case Some(adt: Adt) =>
          val typVarMapping = adt.typVars zip (args map ttyp)
          AdtType(adt, typVarMapping.toMap)
        case Some(other) =>
          sys.error(s"Did not expect member ${other}")
        case None =>
          assert(args.isEmpty)
          TypeVar(name.name) // not a domain, i.e. it must be a type variable
      }
    case PWandType() => Wand
    case t: PExtender => t.translateType(this)
    case PUnknown() =>
      sys.error("unknown type unexpected here")
    case PPredicateType() =>
      sys.error("unexpected use of internal typ")
  }
}

object Translator {
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

  def toInfo(annotations: Seq[PAnnotation], node: PNode): Info = {
    if (annotations.isEmpty) {
      NoInfo
    } else {
      AnnotationInfo(annotations.groupBy(_.key).map{ case (k, v) => k -> v.flatMap(_.values) })
    }
  }
}
