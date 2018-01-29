/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import scala.language.implicitConversions
import scala.collection.mutable
import viper.silver.ast._
import viper.silver.ast.utility._
import viper.silver.FastMessaging

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
case class Translator(program: PProgram, enableFunctionTerminationChecks: Boolean) {
  def translate: Option[Program] /*(Program, Seq[Messaging.Record])*/ = {
    // assert(TypeChecker.messagecount == 0, "Expected previous phases to succeed, but found error messages.") // AS: no longer sharing state with these phases

    program match {
      case PProgram(_, _, pdomains, pfields, pfunctions, ppredicates, pmethods, _) =>
        (pdomains ++ pfields ++ pfunctions ++ ppredicates ++
            pmethods ++ (pdomains flatMap (_.funcs))) foreach translateMemberSignature

        var domain = pdomains map translate
        val fields = pfields map translate
        var functions = pfunctions map translate
        val predicates = ppredicates map translate
        var methods = pmethods map translate

        if (enableFunctionTerminationChecks) {
          // Add methods, domains and functions needed for proving termination
          val termCheck = new DecreasesClause(members)
          val structureForTermProofs = termCheck.addMethods(functions, predicates, domain, members.get("decreasing"), members.get("bounded"), members.get("nested"), members.get("Loc"))
          domain = structureForTermProofs._1
          functions ++= structureForTermProofs._2
          methods ++= structureForTermProofs._3
        }

        val finalProgram = Program(domain, fields, functions, predicates, methods)(program)

        if (Consistency.messages.isEmpty) Some(finalProgram) // all error messages generated during translation should be Consistency messages
        else None
    }
  }

  private def translate(m: PMethod): Method = m match {
    case PMethod(name, _, _, pres, posts, body) =>
      val m = findMethod(name)

      val newBody = body.map(actualBody => {
        val b = stmt(actualBody).asInstanceOf[Seqn]
        val newScopedDecls = b.scopedDecls ++ b.deepCollect {case l: Label => l}

        b.copy(scopedDecls = newScopedDecls)(b.pos, b.info, b.errT)
      })

      val finalMethod = m.copy(pres = pres map exp, posts = posts map exp, body = newBody)(m.pos, m.info, m.errT)

      members(m.name) = finalMethod

      finalMethod
  }

  private def translate(d: PDomain): Domain = d match {
    case PDomain(name, _, functions, axioms) =>
      val d = findDomain(name)
      val dd = d.copy(functions = functions map (f => findDomainFunction(f.idndef)),
        axioms = axioms map translate)(d.pos, d.info, d.errT)
      members(d.name) = dd
      dd
  }

  private def translate(a: PAxiom): DomainAxiom = a match {
    case pa@PAxiom(name, e) =>
      DomainAxiom(name.name, exp(e))(a,domainName = pa.domainName.name)
  }

  private def translate(f: PFunction): Function = f match {
    case PFunction(name, _, _, pres, posts, decs, body) =>
      val f = findFunction(name)
      val ff = f.copy(pres = pres map exp, posts = posts map exp, decs = decs map dec, body = body map exp)(f.pos, f.info, f.errT)
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

  /**
    * Translate the signature of a member, so that it can be looked up later.
    *
    * TODO: Get rid of this method!
    *         - Passing lots of null references is just asking for trouble
    *         - It should no longer be necessary to have this lookup table because, e.g. a
    *           method call no longer needs the method node, the method name (as a string)
    *           suffices
    */
  private def translateMemberSignature(p: PMember) {
    val pos = p
    val name = p.idndef.name
    val t = p match {
      case PField(_, typ) =>
        Field(name, ttyp(typ))(pos)
      case PFunction(_, formalArgs, typ, _, _, _, _) =>
        Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null, null)(pos)
      case pdf@ PDomainFunction(_, args, typ, unique) =>
        DomainFunc(name, args map liftVarDecl, ttyp(typ), unique)(pos,NoInfo,pdf.domainName.name)
      case PDomain(_, typVars, _, _) =>
        Domain(name, null, null, typVars map (t => TypeVar(t.idndef.name)))(pos)
      case PPredicate(_, formalArgs, _) =>
        Predicate(name, formalArgs map liftVarDecl, null)(pos)
      case PMethod(_, formalArgs, formalReturns, _, _, _) =>
        Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null)(pos)
    }
    members.put(p.idndef.name, t)
  }

  // helper methods that can be called if one knows what 'id' refers to
  private def findDomain(id: PIdentifier) = members(id.name).asInstanceOf[Domain]
  private def findField(id: PIdentifier) = members(id.name).asInstanceOf[Field]
  private def findFunction(id: PIdentifier) = members(id.name).asInstanceOf[Function]
  private def findDomainFunction(id: PIdentifier) = members(id.name).asInstanceOf[DomainFunc]
  private def findPredicate(id: PIdentifier) = members(id.name).asInstanceOf[Predicate]
  private def findMethod(id: PIdentifier) = members(id.name).asInstanceOf[Method]

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  private def stmt(s: PStmt): Stmt = {
    val pos = s
    s match {
      case PVarAssign(idnuse, PCall(func, args, _)) if members(func.name).isInstanceOf[Method] =>
        /* This is a method call that got parsed in a slightly confusing way.
         * TODO: Get rid of this case! There is a matching case in the resolver.
         */
        val call = PMethodCall(Seq(idnuse), func, args)
        call.setPos(s)
        stmt(call)
      case PVarAssign(idnuse, rhs) =>
        LocalVarAssign(LocalVar(idnuse.name)(ttyp(idnuse.typ), pos), exp(rhs))(pos)
      case PFieldAssign(field, rhs) =>
        FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnuse))(field), exp(rhs))(pos)
      case PLocalVarDecl(idndef, t, Some(init)) =>
        LocalVarAssign(LocalVar(idndef.name)(ttyp(t), pos), exp(init))(pos)
      case PLocalVarDecl(_, _, None) =>
        // there are no declarations in the Viper AST; rather they are part of the scope signature
        Statements.EmptyStmt
      case PSeqn(ss) =>
        val plocals = ss.collect {
          case l: PLocalVarDecl => Some(l)
          case _ => None
        }
        val locals = plocals.flatten.map {
          case p@PLocalVarDecl(idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(p)
        }
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
      case assume@PAssume(e) =>
        val sub = exp(e)
        if(!sub.isPure) { Consistency.messages ++= FastMessaging.message(assume, "assume statements can only have pure parameters, found: " + sub) }
        Inhale(exp(e))(pos)
      case PExhale(e) =>
        Exhale(exp(e))(pos)
      case PAssert(e) =>
        Assert(exp(e))(pos)
      case PNewStmt(target, fieldsOpt) =>
        val fields = fieldsOpt match {
          case None => program.fields map translate
            /* Slightly redundant since we already translated the fields when we
             * translated the PProgram at the beginning of this class.
             */
          case Some(pfields) => pfields map findField
        }
        NewStmt(exp(target).asInstanceOf[LocalVar], fields)(pos)
      case PMethodCall(targets, method, args) =>
        val ts = (targets map exp).asInstanceOf[Seq[LocalVar]]
        MethodCall(findMethod(method), args map exp, ts)(pos)
      case PLabel(name, invs) =>
        Label(name.name, invs map exp)(pos)
      case PGoto(label) =>
        Goto(label.name)(pos)
      case PIf(cond, thn, els) =>
        If(exp(cond), stmt(thn).asInstanceOf[Seqn], stmt(els).asInstanceOf[Seqn])(pos)
      case PFresh(vars) => Fresh(vars map (v => LocalVar(v.name)(ttyp(v.typ), v)))(pos)
      case PConstraining(vars, ss) =>
        Constraining(vars map (v => LocalVar(v.name)(ttyp(v.typ), v)), stmt(ss).asInstanceOf[Seqn])(pos)
      case PWhile(cond, invs, body) =>
        While(exp(cond), invs map exp, stmt(body).asInstanceOf[Seqn])(pos)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  private def dec(pdec: PDecClause): DecClause = {
    pdec match {
      case PDecStar() => DecStar()(pdec)
      case PDecTuple(d) => DecTuple(d map exp)(pdec)
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  private def exp(pexp: PExp): Exp = {
    val pos = pexp
    pexp match {

      case piu @ PIdnUse(name) =>
        piu.decl match {
          case _: PLocalVarDecl | _: PFormalArgDecl => LocalVar(name)(ttyp(pexp.typ), pos)
          case pf: PField =>
            /* A malformed AST where a field is dereferenced without a receiver */
            Consistency.messages ++= FastMessaging.message(piu, s"expected expression but found field $name")
            LocalVar(pf.idndef.name)(ttyp(pf.typ), pos)
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
            assert(r.typ==Int)
            l.typ match {
              case Perm => PermDiv(l, r)(pos)
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
          case "in" =>
            if (right.typ.isInstanceOf[PSeqType])
              SeqContains(l, r)(pos)
            else
              AnySetContains(l, r)(pos)
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
          case "+" => e
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
        var par: PNode = p.parent
        while (!par.isInstanceOf[PFunction]) {
          if (par == null) sys.error("cannot use 'result' outside of function")
          par = par.parent
        }
        Result()(ttyp(par.asInstanceOf[PFunction].typ), pos)
      case PBoolLit(b) =>
        if (b) TrueLit()(pos) else FalseLit()(pos)
      case PNullLit() =>
        NullLit()(pos)
      case PFieldAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos)
      case PPredicateAccess(args, idn) =>
        PredicateAccess(args map exp, findPredicate(idn).name)(pos)
      case pfa@PCall(func, args, _) =>
        members(func.name) match {
          case f: Function => FuncApp(f, args map exp)(pos)
          case f @ DomainFunc(_, _, _, _) =>
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
                DomainFuncApp(f, actualArgs, sp)(pos)
              case _ => sys.error("type unification error - should report and not crash")
            }
          case _: Predicate =>
            val inner = PredicateAccess(args map exp, findPredicate(func).name) (pos)
            val fullPerm = FullPerm()(pos)
            PredicateAccessPredicate(inner, fullPerm) (pos)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PUnfolding(loc, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos)
      case PApplying(wand, e) =>
        Applying(exp(wand).asInstanceOf[MagicWand], exp(e))(pos)
      case PLet(exp1, PLetNestedScope(variable, body)) =>
        Let(liftVarDecl(variable), exp(exp1), exp(body))(pos)
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(vars, e) =>
        Exists(vars map liftVarDecl, exp(e))(pos)
      case PForall(vars, triggers, e) =>
        val ts = triggers map (t => Trigger(t.exp map exp)(t))
        val fa = Forall(vars map liftVarDecl, ts, exp(e))(pos)
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugareSourceSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      case f@PForPerm(_, args, e) =>

        //val args = fields map findField

        //check that the arguments contain only fields and predicates
        args.foreach(a => Consistency.checkForPermArguments(members(a.name)))

        val argAccess = mutable.Buffer[Location]()
        for (a <- args) {

          //we are either dealing with predicates, or fields!
          members(a.name) match {
            case f : Field => argAccess += f
            case p : Predicate => argAccess += p
            case _ => sys.error("Internal Error: Can only handle fields and predicates in forperm")
          }
        }

        ForPerm(liftVarDecl(f.variable), argAccess.toList, exp(e))(pos)
      case POld(e) =>
        Old(exp(e))(pos)
      case PLabelledOld(lbl,e) =>
        LabelledOld(exp(e),lbl.name)(pos)
      case PCondExp(cond, thn, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos)
      case PCurPerm(loc) =>
        exp(loc) match {
          case PredicateAccessPredicate(inner, _) => CurrentPerm(inner.asInstanceOf[LocationAccess])(pos)
          case x: FieldAccess => CurrentPerm(x.asInstanceOf[LocationAccess])(pos)
          case x: PredicateAccess => CurrentPerm(x.asInstanceOf[LocationAccess])(pos)
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
      case PSeqIndex(seq, idx) =>
        SeqIndex(exp(seq), exp(idx))(pos)
      case PSeqTake(seq, n) =>
        SeqTake(exp(seq), exp(n))(pos)
      case PSeqDrop(seq, n) =>
        SeqDrop(exp(seq), exp(n))(pos)
      case PSeqUpdate(seq, idx, elem) =>
        SeqUpdate(exp(seq), exp(idx), exp(elem))(pos)
      case PSize(s) =>
        if (s.typ.isInstanceOf[PSeqType])
          SeqLength(exp(s))(pos)
        else
          AnySetCardinality(exp(s))(pos)
      case PEmptySet(_) =>
        EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType))(pos)
      case PExplicitSet(elems) =>
        ExplicitSet(elems map exp)(pos)
      case PEmptyMultiset(_) =>
        EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType))(pos)
      case PExplicitMultiset(elems) =>
        ExplicitMultiset(elems map exp)(pos)
    }
  }

  /** Takes a [[viper.silver.parser.FastPositioned]] and turns it into a [[viper.silver.ast.SourcePosition]]. */
  implicit def liftPos(pos: FastPositioned): SourcePosition = {
    val start = LineColumnPosition(pos.start.line, pos.start.column)
    val end = LineColumnPosition(pos.finish.line, pos.finish.column)
    pos.start match {
      case fp: FilePosition => SourcePosition(fp.file, start, end)
      case _ =>
        //FIXME Do we really need to construct an instance of SourcePosition with undefined file field?
        //FIXME One would expect to have a well-defined file path once a position pattern matched this type.
        //FIXME @see https://bitbucket.org/viperproject/silver/issues/232
        SourcePosition(null, start, end)
    }
  }

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVar`. */
  private def liftVarDecl(formal: PFormalArgDecl) =
    LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(formal)

  /** Takes a `PType` and turns it into a `Type`. */
  private def ttyp(t: PType): Type = t match {
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
    case PDomainType(name, args) =>
      members.get(name.name) match {
        case Some(d) =>
          val domain = d.asInstanceOf[Domain]
          val typVarMapping = domain.typVars zip (args map ttyp)
          DomainType(domain, typVarMapping /*.filter {
            case (tv, tt) => tv!=tt //!tt.isInstanceOf[TypeVar]
          }*/.toMap)
        case None =>
          assert(args.isEmpty)
          TypeVar(name.name) // not a domain, i.e. it must be a type variable
      }
    case PWandType() => Wand
    case PUnknown() =>
      sys.error("unknown type unexpected here")
    case PPredicateType() =>
      sys.error("unexpected use of internal typ")
  }
}
