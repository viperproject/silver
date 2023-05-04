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
        pdomains flatMap (_.funcs) foreach translateMemberSignature
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
    case PMethod(name, _, _, pres, posts, body) =>
      val m = findMethod(name)

      val newBody = body.map(actualBody => {
        val b = stmt(actualBody).asInstanceOf[Seqn]
        val newScopedDecls = b.scopedSeqnDeclarations ++ b.deepCollect {case l: Label => l}

        b.copy(scopedSeqnDeclarations = newScopedDecls)(b.pos, b.info, b.errT)
      })

      val finalMethod = m.copy(pres = pres map exp, posts = posts map exp, body = newBody)(m.pos, m.info, m.errT)

      members(m.name) = finalMethod

      finalMethod
  }

  private def translate(d: PDomain): Domain = d match {
    case PDomain(name, _, functions, axioms, interpretation) =>
      val d = findDomain(name)
      val dd = d.copy(functions = functions map (f => findDomainFunction(f.idndef)),
        axioms = axioms map translate, interpretations = interpretation)(d.pos, d.info, d.errT)
      members(d.name) = dd
      dd
  }

  private def translate(a: PAxiom): DomainAxiom = a match {
    case pa@PAxiom(Some(name), e) =>
      NamedDomainAxiom(name.name, exp(e))(a, domainName = pa.domainName.name)
    case pa@PAxiom(None, e) =>
      AnonymousDomainAxiom(exp(e))(a, domainName = pa.domainName.name)
  }

  private def translate(f: PFunction): Function = f match {
    case PFunction(name, _, _, pres, posts, body) =>
      val f = findFunction(name)
      val ff = f.copy( pres = pres map exp, posts = posts map exp, body = body map exp)(f.pos, f.info, f.errT)
      members(f.name) = ff
      ff
  }

  private def translate(p: PPredicate): Predicate = p match {
    case PPredicate(name, _, body) =>
      val p = findPredicate(name)
      val pp = p.copy(body = body map exp)(p.pos, p.info, p.errT)
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
      case PField(_, typ) =>
        Field(name, ttyp(typ))(pos)
      case PFunction(_, formalArgs, typ, _, _, _) =>
        Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null)(pos)
      case pdf@ PDomainFunction(_, args, typ, unique, interp) =>
        DomainFunc(name, args map liftAnyVarDecl, ttyp(typ), unique, interp)(pos,NoInfo,pdf.domainName.name)
      case PDomain(_, typVars, _, _, interp) =>
        Domain(name, null, null, typVars map (t => TypeVar(t.idndef.name)), interp)(pos)
      case PPredicate(_, formalArgs, _) =>
        Predicate(name, formalArgs map liftVarDecl, null)(pos)
      case PMethod(_, formalArgs, formalReturns, _, _, _) =>
        Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null)(pos)
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
  def stmt(s: PStmt): Stmt = {
    val pos = s
    s match {
      case PAssign(targets, PCall(method, args, _)) if members(method.name).isInstanceOf[Method] =>
        val ts = (targets map (exp(_).asInstanceOf[Lhs]))
        MethodCall(findMethod(method), args map exp, ts)(pos)
      case PAssign(targets, _) if targets.length != 1 =>
        sys.error(s"Found non-unary target of assignment")
      case PAssign(Seq(target), PNewExp(fieldsOpt)) =>
        val lhs = exp(target).asInstanceOf[Lhs]
        val fields = fieldsOpt match {
          case None => program.fields map translate
            /* Slightly redundant since we already translated the fields when we
             * translated the PProgram at the beginning of this class.
             */
          case Some(pfields) => pfields map findField
        }
        NewStmt(lhs, fields)(pos)
      case PAssign(Seq(idnuse: PIdnUse), rhs) =>
        Assign(LocalVar(idnuse.name, ttyp(idnuse.typ))(pos), exp(rhs))(pos)
      case PAssign(Seq(field: PFieldAccess), rhs) =>
        Assign(FieldAccess(exp(field.rcv), findField(field.idnuse))(field), exp(rhs))(pos)
      case PLocalVarDecl(_, init) =>
        // there are no declarations in the Viper AST; rather they are part of the scope signature
        init match {
          case Some(assign) => stmt(assign)
          case None => Statements.EmptyStmt
        }
      case PSeqn(ss) =>
        val plocals = ss.collect {
          case l: PLocalVarDecl => Some(l)
          case _ => None
        }
        val locals = plocals.flatten.map {
          case p@PLocalVarDecl(vars, _) => vars.map(v => LocalVarDecl(v.idndef.name, ttyp(v.typ))(p))
        }.flatten
        Seqn(ss filterNot (_.isInstanceOf[PSkip]) map stmt, locals)(pos)
      case PFold(e) =>
        Fold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos)
      case PUnfold(e) =>
        Unfold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos)
      case PPackageWand(e, proofScript) =>
        val wand = exp(e).asInstanceOf[MagicWand]
        Package(wand, stmt(proofScript).asInstanceOf[Seqn])(pos)
      case PApplyWand(e) =>
        Apply(exp(e).asInstanceOf[MagicWand])(pos)
      case PInhale(e) =>
        Inhale(exp(e))(pos)
      case PAssume(e) =>
        Assume(exp(e))(pos)
      case PExhale(e) =>
        Exhale(exp(e))(pos)
      case PAssert(e) =>
        Assert(exp(e))(pos)
      case PLabel(name, invs) =>
        Label(name.name, invs map exp)(pos)
      case PGoto(label) =>
        Goto(label.name)(pos)
      case PIf(cond, thn, els) =>
        If(exp(cond), stmt(thn).asInstanceOf[Seqn], stmt(els).asInstanceOf[Seqn])(pos)
      case PWhile(cond, invs, body) =>
        While(exp(cond), invs map exp, stmt(body).asInstanceOf[Seqn])(pos)
      case PQuasihavoc(lhs, e) =>
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavoc(newLhs, newE)(pos)
      case PQuasihavocall(vars, lhs, e) =>
        val newVars = vars map liftVarDecl
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavocall(newVars, newLhs, newE)(pos)
      case t: PExtender =>   t.translateStmt(this)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }
  }

  /** Helper function that translates subexpressions common to a Havoc or Havocall statement */
  def havocStmtHelper(lhs: Option[PExp], e: PExp): (Option[Exp], ResourceAccess) = {
    val newLhs = lhs.map(exp)
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

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(pexp: PExp): Exp = {
    val pos = pexp
    pexp match {

      case piu @ PIdnUse(name) =>
        piu.decl match {
          case _: PLocalVarDecl | _: PFormalArgDecl => LocalVar(name, ttyp(pexp.typ))(pos)
          case pf: PField =>
            /* A malformed AST where a field is dereferenced without a receiver */
            Consistency.messages ++= FastMessaging.message(piu, s"expected expression but found field $name")
            LocalVar(pf.idndef.name, ttyp(pf.typ))(pos)
          case _ =>
            sys.error("should not occur in type-checked program")
        }
      case pbe @ PBinExp(left, op, right) =>
        val (l, r) = (exp(left), exp(right))
        op match {
          case "+" =>
            r.typ match {
              case Int => Add(l, r)(pos)
              case Perm => PermAdd(l, r)(pos)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "-" =>
            r.typ match {
              case Int => Sub(l, r)(pos)
              case Perm => PermSub(l, r)(pos)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "*" =>
            r.typ match {
              case Int =>
                l.typ match {
                  case Int => Mul(l, r)(pos)
                  case Perm => IntPermMul(r, l)(pos)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case Perm =>
                l.typ match {
                  case Int => IntPermMul(l, r)(pos)
                  case Perm => PermMul(l, r)(pos)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case _ => sys.error("should not occur in type-checked program")
            }
          case "/" =>
            l.typ match {
              case Perm => r.typ match {
                case Int => PermDiv(l, r)(pos)
                case Perm => PermPermDiv(l, r)(pos)
              }
              case Int  =>
                assert (r.typ==Int)
                if (ttyp(pbe.typ) == Int)
                  Div(l, r)(pos)
                else
                  FractionalPerm(l, r)(pos)
              case _    => sys.error("should not occur in type-checked program")
            }
          case "\\" => Div(l, r)(pos)
          case "%" => Mod(l, r)(pos)
          case "<" =>
            l.typ match {
              case Int => LtCmp(l, r)(pos)
              case Perm => PermLtCmp(l, r)(pos)
              case _ => sys.error("unexpected type")
            }
          case "<=" =>
            l.typ match {
              case Int => LeCmp(l, r)(pos)
              case Perm => PermLeCmp(l, r)(pos)
              case _ => sys.error("unexpected type")
            }
          case ">" =>
            l.typ match {
              case Int => GtCmp(l, r)(pos)
              case Perm => PermGtCmp(l, r)(pos)
              case _ => sys.error("unexpected type")
            }
          case ">=" =>
            l.typ match {
              case Int => GeCmp(l, r)(pos)
              case Perm => PermGeCmp(l, r)(pos)
              case _ => sys.error("unexpected type")
            }
          case "==" => EqCmp(l, r)(pos)
          case "!=" => NeCmp(l, r)(pos)
          case "==>" => Implies(l, r)(pos)
          case "--*" => MagicWand(l, r)(pos)
          case "<==>" => EqCmp(l, r)(pos)
          case "&&" => And(l, r)(pos)
          case "||" => Or(l, r)(pos)

          case "in" => right.typ match {
            case _: PSeqType => SeqContains(l, r)(pos)
            case _: PMapType => MapContains(l, r)(pos)
            case _: PSetType | _: PMultisetType => AnySetContains(l, r)(pos)
            case t => sys.error(s"unexpected type $t")
          }

          case "++" => SeqAppend(l, r)(pos)
          case "subset" => AnySetSubset(l, r)(pos)
          case "intersection" => AnySetIntersection(l, r)(pos)
          case "union" => AnySetUnion(l, r)(pos)
          case "setminus" => AnySetMinus(l, r)(pos)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op match {
          case "-" =>
            e.typ match {
              case Int => Minus(e)(pos)
              case Perm => PermMinus(e)(pos)
              case _ => sys.error("unexpected type")
            }
          case "!" => Not(e)(pos)
        }
      case PInhaleExhaleExp(in, ex) =>
        InhaleExhaleExp(exp(in), exp(ex))(pos)
      case PIntLit(i) =>
        IntLit(i)(pos)
      case p@PResultLit() =>
        // find function
        var par: PNode = p.parent.get
        while (!par.isInstanceOf[PFunction]) {
          if (par == null) sys.error("cannot use 'result' outside of function")
          par = par.parent.get
        }
        Result(ttyp(par.asInstanceOf[PFunction].typ))(pos)
      case PBoolLit(b) =>
        if (b) TrueLit()(pos) else FalseLit()(pos)
      case PNullLit() =>
        NullLit()(pos)
      case PFieldAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos)
      case PPredicateAccess(args, idn) =>
        PredicateAccess(args map exp, findPredicate(idn).name)(pos)
      case PMagicWandExp(left, right) => MagicWand(exp(left), exp(right))(pos)
      case pfa@PCall(func, args, _) =>
        members(func.name) match {
          case f: Function => FuncApp(f, args map exp)(pos)
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
                  BackendFuncApp(f, actualArgs)(pos)
                else
                  DomainFuncApp(f, actualArgs, sp)(pos)
              case _ => sys.error("type unification error - should report and not crash")
            }
          case _: Predicate =>
            val inner = PredicateAccess(args map exp, findPredicate(func).name) (pos)
            val fullPerm = FullPerm()(pos)
            PredicateAccessPredicate(inner, fullPerm) (pos)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PNewExp(_) => sys.error("unexpected `new` expression")
      case PUnfolding(loc, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos)
      case PApplying(wand, e) =>
        Applying(exp(wand).asInstanceOf[MagicWand], exp(e))(pos)
      case PLet(exp1, PLetNestedScope(variable, body)) =>
        Let(liftVarDecl(variable), exp(exp1), exp(body))(pos)
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(vars, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        Exists(vars map liftVarDecl, ts, exp(e))(pos)
      case PForall(vars, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        val fa = Forall(vars map liftVarDecl, ts, exp(e))(pos)
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      case PForPerm(vars, res, e) =>
        val varList = vars map liftVarDecl
        exp(res) match {
          case PredicateAccessPredicate(inner, _) => ForPerm(varList, inner, exp(e))(pos)
          case f : FieldAccess => ForPerm(varList, f, exp(e))(pos)
          case p : PredicateAccess => ForPerm(varList, p, exp(e))(pos)
          case w : MagicWand => ForPerm(varList, w, exp(e))(pos)
          case other =>
            sys.error(s"Internal Error: Unexpectedly found $other in forperm")
        }
      case POld(e) =>
        Old(exp(e))(pos)
      case PLabelledOld(lbl,e) =>
        LabelledOld(exp(e),lbl.name)(pos)
      case PCondExp(cond, thn, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos)
      case PCurPerm(res) =>
        exp(res) match {
          case PredicateAccessPredicate(inner, _) => CurrentPerm(inner)(pos)
          case x: FieldAccess => CurrentPerm(x)(pos)
          case x: PredicateAccess => CurrentPerm(x)(pos)
          case x: MagicWand => CurrentPerm(x)(pos)
          case other => sys.error(s"Unexpectedly found $other")
        }
      case PNoPerm() =>
        NoPerm()(pos)
      case PFullPerm() =>
        FullPerm()(pos)
      case PWildcard() =>
        WildcardPerm()(pos)
      case PEpsilon() =>
        EpsilonPerm()(pos)
      case PAccPred(loc, perm) =>
        val p = exp(perm)
        exp(loc) match {
          case loc@FieldAccess(_, _) =>
            FieldAccessPredicate(loc, p)(pos)
          case loc@PredicateAccess(_, _) =>
            PredicateAccessPredicate(loc, p)(pos)
          case PredicateAccessPredicate(inner, _) => PredicateAccessPredicate(inner, p)(pos)
          case _ =>
            sys.error("unexpected location")
        }
      case PEmptySeq(_) =>
        EmptySeq(ttyp(pexp.typ.asInstanceOf[PSeqType].elementType))(pos)
      case PExplicitSeq(elems) =>
        ExplicitSeq(elems map exp)(pos)
      case PRangeSeq(low, high) =>
        RangeSeq(exp(low), exp(high))(pos)

      case PLookup(base, index) => base.typ match {
        case _: PSeqType => SeqIndex(exp(base), exp(index))(pos)
        case _: PMapType => MapLookup(exp(base), exp(index))(pos)
        case t => sys.error(s"unexpected type $t")
      }

      case PSeqTake(seq, n) =>
        SeqTake(exp(seq), exp(n))(pos)
      case PSeqDrop(seq, n) =>
        SeqDrop(exp(seq), exp(n))(pos)

      case PUpdate(base, key, value) => base.typ match {
        case _: PSeqType => SeqUpdate(exp(base), exp(key), exp(value))(pos)
        case _: PMapType => MapUpdate(exp(base), exp(key), exp(value))(pos)
        case t => sys.error(s"unexpected type $t")
      }

      case PSize(base) => base.typ match {
        case _: PSeqType => SeqLength(exp(base))(pos)
        case _: PMapType => MapCardinality(exp(base))(pos)
        case _: PSetType | _: PMultisetType => AnySetCardinality(exp(base))(pos)
        case t => sys.error(s"unexpected type $t")
      }

      case PEmptySet(_) =>
        EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType))(pos)
      case PExplicitSet(elems) =>
        ExplicitSet(elems map exp)(pos)
      case PEmptyMultiset(_) =>
        EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType))(pos)
      case PExplicitMultiset(elems) =>
        ExplicitMultiset(elems map exp)(pos)

      case PEmptyMap(_, _) => EmptyMap(
        ttyp(pexp.typ.asInstanceOf[PMapType].keyType),
        ttyp(pexp.typ.asInstanceOf[PMapType].valueType)
      )(pos)
      case PExplicitMap(elems) =>
        ExplicitMap(elems map exp)(pos)
      case PMaplet(key, value) =>
        Maplet(exp(key), exp(value))(pos)
      case PMapDomain(base) =>
        MapDomain(exp(base))(pos)
      case PMapRange(base) =>
        MapRange(exp(base))(pos)

      case t: PExtender => t.translateExp(this)
    }
  }

  /** Takes a [[viper.silver.parser.FastPositioned]] and turns it into a [[viper.silver.ast.SourcePosition]]. */
  implicit def liftPos(node: Where): SourcePosition = {
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
    case PPrimitiv(name) => name match {
      case "Int" => Int
      case "Bool" => Bool
      case "Ref" => Ref
      case "Perm" => Perm
    }
    case PSeqType(elemType) =>
      SeqType(ttyp(elemType))
    case PSetType(elemType) =>
      SetType(ttyp(elemType))
    case PMultisetType(elemType) =>
      MultisetType(ttyp(elemType))
    case PMapType(keyType, valueType) =>
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
