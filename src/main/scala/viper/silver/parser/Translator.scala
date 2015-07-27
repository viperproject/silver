/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import language.implicitConversions
import org.kiama.attribution.Attributable
import org.kiama.util.Messaging
import org.kiama.util.{Positioned => KiamaPositioned}
import viper.silver.ast._
import viper.silver.ast.utility.{Visitor, Statements}
import scala.collection.immutable.HashSet

/**
 * Takes an abstract syntax tree after parsing is done and translates it into
 * a SIL abstract syntax tree.
 *
 * [2014-05-08 Malte] The current architecture of the resolver makes it hard
 * to detect all malformed ASTs. It is, for example, hard to detect that an
 * expression "f > 0", where f is an int-typed field, is malformed.
 * The translator can thus not assume that the input tree is completely
 * wellformed, and in cases where a malformed tree is detected, it does not
 * return a tree, but instead, records error messages using Kiama's
 * Messaging feature.
 */
case class Translator(program: PProgram) {
  val file = program.file

  def translate: Option[Program] /*(Program, Seq[Messaging.Record])*/ = {
    assert(Messaging.messagecount == 0, "Expected previous phases to succeed, but found error messages.")

    program match {
      case PProgram(_, pdomains, pfields, pfunctions, ppredicates, pmethods) =>
        (pdomains ++ pfields ++ pfunctions ++ ppredicates ++
            pmethods ++ (pdomains flatMap (_.funcs))) map translateMemberSignature

        val domain = pdomains map (translate(_))
        val fields = pfields map (translate(_))
        val functions = pfunctions map (translate(_))
        val predicates = ppredicates map (translate(_))
        val methods = pmethods map (translate(_))
        val prog = Program(domain, fields, functions, predicates, methods)(program)

        if (Messaging.messagecount == 0) Some(prog)
        else None
    }
  }

  private def translate(pm: PMethod): Method = pm match {
    case PMethod(name, formalArgs, formalReturns, pres, posts, body) =>
      val m = findMethod(name)
      val plocals = Visitor.shallowCollect(body.childStmts, Nodes.subnodes)({
        case l: PLocalVarDecl => Some(l)
        case w: PWhile => None
      }).flatten // only collect declarations at top-level, not from nested loop bodies
      val locals = plocals map {
        case p@PLocalVarDecl(idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(p)
      }
      m.locals = locals
      m.pres = pres map exp
      m.posts = posts map exp
      m.body = stmt(body)
      m
  }

  private def translate(d: PDomain): Domain = d match {
    case PDomain(name, typVars, functions, axioms) =>
      val d = findDomain(name)
      d.functions = functions map (f => findDomainFunction(f.idndef))
      d.axioms = axioms map (translate(_))
      d
  }

  private def translate(a: PAxiom): DomainAxiom = a match {
    case PAxiom(name, e) =>
      DomainAxiom(name.name, exp(e))(a)
  }

  private def translate(pf: PFunction):Function = pf match {
    case PFunction(name, formalArgs, typ, pres, posts, body) =>
      val f = findFunction(name)
      f.pres = pres map exp
      f.posts = posts map exp
      f.body = body map exp
      f
  }

  private def translate(p: PPredicate) = p match {
    case PPredicate(name, formalArgs, body) =>
      val p = findPredicate(name)
      p.body = body map exp
      p
  }

  private def translate(f: PField) = findField(f.idndef)

  private val predefinedAttributes = scala.collection.mutable.HashSet[String](
    ""
  )

  def isPredefinedAttribute(s:String) = predefinedAttributes.contains(s)

  private val getAttrConstructor = scala.collection.mutable.HashMap[String, (Seq[PAttributeValue]) => Option[Attribute]](
    "" -> ((_:Seq[PAttributeValue]) => sys.error("unexpected empty attribute key"))
  ).withDefaultValue((_:Seq[PAttributeValue]) => None:Option[Attribute])

  def addAttributeConstructor(key:String, f:Seq[PAttributeValue] => Option[Attribute]) = {
    predefinedAttributes += key
    getAttrConstructor += (key -> f)
  }

  def translate(pa:PAttribute): Attribute = getAttrConstructor(pa.key)(pa.values) match {
    case Some(e@ValuedAttribute("-error", Seq(StringValue(msg)))) => {
      Messaging.message(pa,msg);
      e
    }
    case Some(a:Attribute) =>
      a
    case None => {
      if(isPredefinedAttribute(pa.key)) pa.key match{
        case "verified-if" =>
          Messaging.message(pa, "Value for attribute \"verified-if\" must be pure\n")
        case _ => Messaging.message(pa,"There was an issue with translating the attribute with key " + pa.key)
      }
      pa.values match {
        case Nil => OrdinaryAttribute(pa.key)
        case vs => ValuedAttribute(pa.key, pa.values map (translate(_)))
      }
    }
  }

  private def translate(v : PAttributeValue) : AttributeValue = v match{
    case v:PStringValue => StringValue(v.value)
    case v:PExpValue => ExpValue(exp(v.value))
    case _ => sys.error("unexpected attribute value parsed")
  }

  private val members = collection.mutable.HashMap[String, Node]()
  /**
   * Translate the signature of a member, so that it can be looked up later.
   */
  private def translateMemberSignature(p: PMember) {
    val pos = p
    val name = p.idndef.name
    val t = p match {
      case PField(_, typ) =>
        Field(name, ttyp(typ))(pos)
      case pf@PFunction(_, formalArgs, typ, _, _, _) =>
        val f = Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null)(pos, attributes = pf.getAttributes.map((pa:PAttribute) => translate(pa)))
        f
      case pdf@PDomainFunction(_, args, typ, unique) =>
        val df = DomainFunc(name, args map liftVarDecl, ttyp(typ), unique)(pos, attributes = pdf.getAttributes.map((pa:PAttribute) => translate(pa)))
        df
      case PDomain(_, typVars, funcs, axioms) =>
        Domain(name, null, null, typVars map (t => TypeVar(t.idndef.name)))(pos)
      case pp@PPredicate(_, formalArgs, _) =>
        Predicate(name, formalArgs map liftVarDecl, null)(pos,attributes = pp.getAttributes.map((pa:PAttribute) => translate(pa)))
      case pm@PMethod(_, formalArgs, formalReturns, _, _, _) =>
        val m = Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null, null)(pos, attributes = pm.getAttributes.map((pa:PAttribute) => translate(pa)))
        m
    }
    members.put(p.idndef.name, t)
  }

  // helper methods that can be called if one knows what 'id' refers to
  private def findDomain(id: PIdentifier) = members.get(id.name).get.asInstanceOf[Domain]
  private def findField(id: PIdentifier) = members.get(id.name).get.asInstanceOf[Field]
  private def findFunction(id: PIdentifier) = members.get(id.name).get.asInstanceOf[Function]
  private def findDomainFunction(id: PIdentifier) = members.get(id.name).get.asInstanceOf[DomainFunc]
  private def findPredicate(id: PIdentifier) = members.get(id.name).get.asInstanceOf[Predicate]
  private def findMethod(id: PIdentifier) = members.get(id.name).get.asInstanceOf[Method]

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  private def stmt(s: PStmt): Stmt = {
    val pos = s
    val atts = s.getAttributes.map((pa:PAttribute) => translate(pa))
    s match {
      case PVarAssign(idnuse, PFunctApp(func, args)) if members.get(func.name).get.isInstanceOf[Method] =>
        /* This is a method call that got parsed in a slightly confusing way.
         * TODO: Get rid of this case! There is a matching case in the resolver.
         */
        val call = PMethodCall(Seq(idnuse), func, args)
        call.setAttributes(s.getAttributes)
        call.setStart(s.start)
        stmt(call)
      case PVarAssign(idnuse, rhs) =>
        LocalVarAssign(LocalVar(idnuse.name)(ttyp(idnuse.typ), pos), exp(rhs))(pos, attributes = atts)
      case PFieldAssign(field, rhs) =>
        FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnuse))(field), exp(rhs))(pos, attributes = atts)
      case PLocalVarDecl(idndef, t, Some(init)) =>
        LocalVarAssign(LocalVar(idndef.name)(ttyp(t), pos), exp(init))(pos, attributes = atts)
      case PLocalVarDecl(_, _, None) =>
        // there are no declarations in the SIL AST; rather they are part of the method signature
        Statements.EmptyStmt
      case PSeqn(ss) =>
        Seqn(ss filterNot (_.isInstanceOf[PSkip]) map stmt)(pos, attributes = atts)
      case PFold(e) =>
        Fold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, attributes = atts)
      case PUnfold(e) =>
        Unfold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, attributes = atts)
      case PInhale(e) =>
        Inhale(exp(e))(pos, attributes = atts)
      case PExhale(e) =>
        Exhale(exp(e))(pos, attributes = atts)
      case PAssert(e) =>
        Assert(exp(e))(pos, attributes = atts)
      case PNewStmt(target, fieldsOpt) =>
        val fields = fieldsOpt match {
          case None => program.fields map (translate(_))
          /* Slightly redundant since we already translated the fields when we
             * translated the PProgram at the beginning of this class.
             */
          case Some(pfields) => pfields map findField
        }
        NewStmt(exp(target).asInstanceOf[LocalVar], fields)(pos, attributes = atts)
      case PMethodCall(targets, method, args) =>
        val ts = (targets map exp).asInstanceOf[Seq[LocalVar]]
        MethodCall(findMethod(method), args map exp, ts)(pos, attributes = atts)
      case PLabel(name) =>
        Label(name.name)(pos, attributes = atts)
      case PGoto(label) =>
        Goto(label.name)(pos, attributes = atts)
      case PIf(cond, thn, els) =>
        If(exp(cond), stmt(thn), stmt(els))(pos, attributes = atts)
      case PFresh(vars) =>
        Fresh(vars map (v => LocalVar(v.name)(ttyp(v.typ), v)))(pos, attributes = atts)
      case PConstraining(vars, ss) =>
        Constraining(vars map (v => LocalVar(v.name)(ttyp(v.typ), v)), stmt(ss))(pos, attributes = atts)
      case PWhile(cond, invs, body) =>
        val plocals = body.childStmts collect {
          // Note: this won't collect declarations from nested loops
          case l: PLocalVarDecl => l
        }
        val locals = plocals map {
          case p@PLocalVarDecl(idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(pos)
        }
        While(exp(cond), invs map exp, locals, stmt(body))(pos, attributes = atts)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(pexp: PExp): Exp = {
    val pos = pexp
    val attrs = pexp.getAttributes map ((a:PAttribute) => translate(a))
    pexp match {
      case piu @ PIdnUse(name) =>
        piu.decl match {
          case _: PLocalVarDecl | _: PFormalArgDecl => LocalVar(name)(ttyp(pexp.typ), pos,attributes = attrs)
          case pf: PField =>
            /* A malformed AST where a field is dereferenced without a receiver */
            Messaging.message(piu, s"expected expression but found field $name")
            LocalVar(pf.idndef.name)(ttyp(pf.typ), pos,attributes = attrs)
          case other =>
            sys.error("should not occur in type-checked program")
        }
      case PBinExp(left, op, right) =>
        val (l, r) = (exp(left), exp(right))
        op match {
          case "+" =>
            r.typ match {
              case Int => Add(l, r)(pos,attributes = attrs)
              case Perm => PermAdd(l, r)(pos,attributes = attrs)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "-" =>
            r.typ match {
              case Int => Sub(l, r)(pos,attributes = attrs)
              case Perm => PermSub(l, r)(pos,attributes = attrs)
              case _ => sys.error("should not occur in type-checked program")
            }
          case "*" =>
            r.typ match {
              case Int => Mul(l, r)(pos,attributes = attrs)
              case Perm =>
                l.typ match {
                  case Int => IntPermMul(l, r)(pos,attributes = attrs)
                  case Perm => PermMul(l, r)(pos,attributes = attrs)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case _ => sys.error("should not occur in type-checked program")
            }
          case "/" =>
            assert(r.typ==Int)
            l.typ match {
              case Perm => PermDiv(l, r)(pos,attributes = attrs)
              case Int  => assert (l.typ==Int); FractionalPerm(l, r)(pos,attributes = attrs)
              case _    => sys.error("should not occur in type-checked program")
            }
          case "\\" => Div(l, r)(pos,attributes = attrs)
          case "%" => Mod(l, r)(pos,attributes = attrs)
          case "<" =>
            l.typ match {
              case Int => LtCmp(l, r)(pos,attributes = attrs)
              case Perm => PermLtCmp(l, r)(pos,attributes = attrs)
              case _ => sys.error("unexpected type")
            }
          case "<=" =>
            l.typ match {
              case Int => LeCmp(l, r)(pos,attributes = attrs)
              case Perm => PermLeCmp(l, r)(pos,attributes = attrs)
              case _ => sys.error("unexpected type")
            }
          case ">" =>
            l.typ match {
              case Int => GtCmp(l, r)(pos,attributes = attrs)
              case Perm => PermGtCmp(l, r)(pos,attributes = attrs)
              case _ => sys.error("unexpected type")
            }
          case ">=" =>
            l.typ match {
              case Int => GeCmp(l, r)(pos,attributes = attrs)
              case Perm => PermGeCmp(l, r)(pos,attributes = attrs)
              case _ => sys.error("unexpected type")
            }
          case "==" => EqCmp(l, r)(pos,attributes = attrs)
          case "!=" => NeCmp(l, r)(pos,attributes = attrs)
          case "==>" => Implies(l, r)(pos,attributes = attrs)
          case "<==>" => EqCmp(l, r)(pos,attributes = attrs)
          case "&&" => And(l, r)(pos,attributes = attrs)
          case "||" => Or(l, r)(pos,attributes = attrs)
          case "in" =>
            if (right.typ.isInstanceOf[PSeqType])
              SeqContains(l, r)(pos)
            else
              AnySetContains(l, r)(pos,attributes = attrs)
          case "++" => SeqAppend(l, r)(pos,attributes = attrs)
          case "subset" => AnySetSubset(l, r)(pos,attributes = attrs)
          case "intersection" => AnySetIntersection(l, r)(pos,attributes = attrs)
          case "union" => AnySetUnion(l, r)(pos,attributes = attrs)
          case "setminus" => AnySetMinus(l, r)(pos,attributes = attrs)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op match {
          case "+" => e
          case "-" => Minus(e)(pos,attributes = attrs)
          case "!" => Not(e)(pos,attributes = attrs)
        }
      case PInhaleExhaleExp(in, ex) =>
        InhaleExhaleExp(exp(in), exp(ex))(pos,attributes = attrs)
      case PIntLit(i) =>
        IntLit(i)(pos,attributes = attrs)
      case p@PResultLit() =>
        // find function
        var par: Attributable = p.parent
        while (!par.isInstanceOf[PFunction]) {
          if (par == null) sys.error("cannot use 'result' outside of function")
          par = par.parent
        }
        Result()(ttyp(par.asInstanceOf[PFunction].typ), pos,attributes = attrs)
      case PBoolLit(b) =>
        if (b) TrueLit()(pos,attributes = attrs) else FalseLit()(pos,attributes = attrs)
      case PNullLit() =>
        NullLit()(pos,attributes = attrs)
      case p@PFieldAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos,attributes = attrs)
      case p@PPredicateAccess(args, idn) =>
        PredicateAccess(args map exp, findPredicate(idn))(pos, NoInfo,attributes = attrs)
      case PFunctApp(func, args) =>
        members.get(func.name).get match {
          case f: Function => FuncApp(f, args map exp)(pos,NoInfo,attributes = attrs)
          case f @ DomainFunc(name, formalArgs, typ, _) =>
            val actualArgs = args map exp
            val translatedTyp = ttyp(pexp.typ)
            // 'learn' looks at the formal type of an expression and the one actually
            // occurring in the program and tries to learn instantiations for type variables.
            def learn(formal: Type, actual: Type): Seq[(TypeVar, Type)] = {
              (formal, actual) match {
                case (tv: TypeVar, t) if t.isConcrete => Seq(tv -> t)
                case (DomainType(_, m1), DomainType(_, m2)) =>
                  m2.toSeq
                case _ => Nil
              }
            }
            // infer the type variable mapping for this call
            val map = learn(typ, translatedTyp) ++
              ((formalArgs map (_.typ)) zip (actualArgs map (_.typ)) flatMap (x => learn(x._1, x._2)))

            DomainFuncApp(f, actualArgs, map.toMap)(pos,NoInfo,attributes = attrs)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PUnfolding(loc, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos,attributes = attrs)
      case PLet(exp1, PLetNestedScope(variable, body)) =>
        Let(liftVarDecl(variable), exp(exp1), exp(body))(pos,attributes = attrs)
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(vars, e) =>
        Exists(vars map liftVarDecl, exp(e))(pos,attributes = attrs)
      case PForall(vars, triggers, e) =>
        val ts = triggers map (exps => Trigger(exps map exp)(exps(0)))
        Forall(vars map liftVarDecl, ts, exp(e))(pos,attributes = attrs)
      case POld(e) =>
        Old(exp(e))(pos,attributes = attrs)
      case PCondExp(cond, thn, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos,attributes = attrs)
      case PCurPerm(loc) =>
        CurrentPerm(exp(loc).asInstanceOf[LocationAccess])(pos,attributes = attrs)
      case PNoPerm() =>
        NoPerm()(pos,attributes = attrs)
      case PFullPerm() =>
        FullPerm()(pos,attributes = attrs)
      case PWildcard() =>
        WildcardPerm()(pos,attributes = attrs)
      case PEpsilon() =>
        EpsilonPerm()(pos,attributes = attrs)
      case PAccPred(loc, perm) =>
        val p = exp(perm)
        exp(loc) match {
          case loc@FieldAccess(rcv, field) =>
            FieldAccessPredicate(loc, p)(pos,attributes = attrs)
          case loc@PredicateAccess(rcv, pred) =>
            PredicateAccessPredicate(loc, p)(pos,attributes = attrs)
          case _ =>
            sys.error("unexpected location")
        }
      case PEmptySeq(_) =>
        EmptySeq(ttyp(pexp.typ.asInstanceOf[PSeqType].elementType))(pos,attributes = attrs)
      case PExplicitSeq(elems) =>
        ExplicitSeq(elems map exp)(pos,attributes = attrs)
      case PRangeSeq(low, high) =>
        RangeSeq(exp(low), exp(high))(pos,attributes = attrs)
      case PSeqIndex(seq, idx) =>
        SeqIndex(exp(seq), exp(idx))(pos,attributes = attrs)
      case PSeqTake(seq, n) =>
        SeqTake(exp(seq), exp(n))(pos,attributes = attrs)
      case PSeqDrop(seq, n) =>
        SeqDrop(exp(seq), exp(n))(pos,attributes = attrs)
      case PSeqUpdate(seq, idx, elem) =>
        SeqUpdate(exp(seq), exp(idx), exp(elem))(pos,attributes = attrs)
      case PSize(s) =>
        if (s.typ.isInstanceOf[PSeqType])
          SeqLength(exp(s))(pos,attributes = attrs)
        else
          AnySetCardinality(exp(s))(pos,attributes = attrs)
      case PEmptySet(_) =>
        EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType))(pos,attributes = attrs)
      case PExplicitSet(elems) =>
        ExplicitSet(elems map exp)(pos,attributes = attrs)
      case PEmptyMultiset(_) =>
        EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType))(pos,attributes = attrs)
      case PExplicitMultiset(elems) =>
        ExplicitMultiset(elems map exp)(pos,attributes = attrs)
    }
  }

//  /** Takes a `scala.util.parsing.input.Position` and turns it into a `SourcePosition`. */
//  implicit def liftPos(pos: scala.util.parsing.input.Position): SourcePosition =
//    SourcePosition(file, pos.line, pos.column)

  /** Takes a [[org.kiama.util.Positioned]] and turns it into a [[viper.silver.ast.SourcePosition]]. */
  implicit def liftPos(pos: KiamaPositioned): SourcePosition = {
    val start = LineColumnPosition(pos.start.line, pos.start.column)
    val end = LineColumnPosition(pos.finish.line, pos.finish.column)
    SourcePosition(file, start, end)
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
          assert(args.length == 0)
          TypeVar(name.name) // not a domain, i.e. it must be a type variable
      }
    case PUnknown() =>
      sys.error("unknown type unexpected here")
    case PPredicateType() =>
      sys.error("unexpected use of internal typ")
  }
}