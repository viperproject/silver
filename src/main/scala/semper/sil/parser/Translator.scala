package semper.sil.parser

import semper.sil.ast._
import utility.Statements
import language.implicitConversions
import org.kiama.attribution.Attributable

/**
 * Takes an abstract syntax tree after parsing is done and translates it into a SIL abstract
 * syntax tree.
 *
 * Note that the translator assumes that the tree is well-formed (it typechecks and follows all the rules
 * of a valid SIL program).  No checks are performed, and the code might crash if the input is malformed.
 */
case class Translator(program: PProgram) {

  def translate: Program = {
    program match {
      case PProgram(domains, fields, functions, predicates, methods) =>
        (domains ++ fields ++ functions ++ predicates ++
          methods ++ (domains flatMap (_.funcs))) map translateMemberSignature
        val d = domains map (translate(_))
        val f = fields map (translate(_))
        val fs = functions map (translate(_))
        val p = predicates map (translate(_))
        val m = methods map (translate(_))
        Program(d, f, fs, p, m)(program.start)
    }
  }

  private def translate(m: PMethod): Method = m match {
    case PMethod(name, formalArgs, formalReturns, pres, posts, body) =>
      val m = findMethod(name)
      val plocals = body.childStmts collect {
        case l: PLocalVarDecl => l
      }
      val locals = plocals map {
        case p@PLocalVarDecl(idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(p.start)
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
      DomainAxiom(name.name, exp(e))(a.start)
  }

  private def translate(f: PFunction) = f match {
    case PFunction(name, formalArgs, typ, pres, posts, body) =>
      val f = findFunction(name)
      f.pres = pres map exp
      f.posts = posts map exp
      f.exp = exp(body)
      f
  }

  private def translate(p: PPredicate) = p match {
    case PPredicate(name, formalArg, body) =>
      val p = findPredicate(name)
      p.body = exp(body)
      p
  }

  private def translate(f: PField) = findField(f.idndef)

  private val members = collection.mutable.HashMap[String, Node]()
  /**
   * Translate the signature of a member, so that it can be looked up later.
   */
  private def translateMemberSignature(p: PMember) {
    val pos = p.start
    val name = p.idndef.name
    val t = p match {
      case PField(_, typ) =>
        Field(name, ttyp(typ))(pos)
      case PFunction(_, formalArgs, typ, _, _, _) =>
        Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null)(pos)
      case PDomainFunction(_, args, typ) =>
        DomainFunc(name, args map liftVarDecl, ttyp(typ))(pos)
      case PDomain(_, typVars, funcs, axioms) =>
        Domain(name, null, null, typVars map (t => TypeVar(t.name)))(pos)
      case PPredicate(_, formalArg, _) =>
        Predicate(name, liftVarDecl(formalArg), null)(pos)
      case PMethod(_, formalArgs, formalReturns, _, _, _) =>
        Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null, null)(pos)
    }
    members.put(p.idndef.name, t)
  }

  // helper methods that can be called if one knows what 'id' refers to
  private def findDomain(id: Identifier) = members.get(id.name).get.asInstanceOf[Domain]
  private def findField(id: Identifier) = members.get(id.name).get.asInstanceOf[Field]
  private def findFunction(id: Identifier) = members.get(id.name).get.asInstanceOf[Function]
  private def findDomainFunction(id: Identifier) = members.get(id.name).get.asInstanceOf[DomainFunc]
  private def findPredicate(id: Identifier) = members.get(id.name).get.asInstanceOf[Predicate]
  private def findMethod(id: Identifier) = members.get(id.name).get.asInstanceOf[Method]

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  private def stmt(s: PStmt): Stmt = {
    val pos = s.start
    s match {
      case PVarAssign(idnuse, rhs) =>
        LocalVarAssign(LocalVar(idnuse.name)(ttyp(idnuse.typ), pos), exp(rhs))(pos)
      case PFieldAssign(field, rhs) =>
        FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnuse))(field.start), exp(rhs))(pos)
      case PLocalVarDecl(idndef, t, Some(init)) =>
        LocalVarAssign(LocalVar(idndef.name)(ttyp(t), pos), exp(init))(pos)
      case PLocalVarDecl(_, _, None) =>
        // there are no declarations in the SIL AST; rather they are part of the method signature
        Statements.EmptyStmt
      case PSeqn(ss) =>
        Seqn(ss map stmt)(pos)
      case PFold(e) =>
        Fold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos)
      case PUnfold(e) =>
        Unfold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos)
      case PInhale(e) =>
        Inhale(exp(e))(pos)
      case PExhale(e) =>
        Exhale(exp(e))(pos)
      case PAssert(e) =>
        Assert(exp(e))(pos)
      case PNewStmt(idnuse) =>
        NewStmt(exp(idnuse).asInstanceOf[LocalVar])(pos)
      case PMethodCall(targets, method, args) =>
        val ts = (targets match {
          case None => Nil
          case Some(t) => t map exp
        }).asInstanceOf[Seq[LocalVar]]
        MethodCall(findMethod(method), args map exp, ts)(pos)
      case PLabel(name) =>
        Label(name.name)(pos)
      case PGoto(label) =>
        Goto(label.name)(pos)
      case PIf(cond, thn, els) =>
        If(exp(cond), stmt(thn), stmt(els))(pos)
      case PWhile(cond, invs, body) =>
        val plocals = body.childStmts collect {
          case l: PLocalVarDecl => l
        }
        val locals = plocals map {
          case p@PLocalVarDecl(idndef, t, _) => LocalVarDecl(idndef.name, ttyp(t))(pos)
        }
        While(exp(cond), invs map exp, locals, stmt(body))(pos)
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  private def exp(pexp: PExp): Exp = {
    val pos = pexp.start
    pexp match {
      case PIdnUse(name) =>
        LocalVar(name)(ttyp(pexp.typ), pos)
      case PBinExp(left, op, right) =>
        val (l, r) = (exp(left), exp(right))
        op match {
          case "+" => Add(l, r)(pos)
          case "-" => Sub(l, r)(pos)
          case "*" => Mul(l, r)(pos)
          case "/" => Div(l, r)(pos)
          case "%" => Mod(l, r)(pos)
          case "<" => LtCmp(l, r)(pos)
          case "<=" => LeCmp(l, r)(pos)
          case ">" => GtCmp(l, r)(pos)
          case ">=" => GeCmp(l, r)(pos)
          case "==" => EqCmp(l, r)(pos)
          case "!=" => NeCmp(l, r)(pos)
          case "==>" => Implies(l, r)(pos)
          case "<==>" => EqCmp(l, r)(pos)
          case "&&" => And(l, r)(pos)
          case "||" => Or(l, r)(pos)
          case "in" => SeqContains(l, r)(pos)
          case "++" => SeqAppend(l, r)(pos)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op match {
          case "+" => e
          case "-" => Neg(e)(pos)
          case "!" => Not(e)(pos)
        }
      case PIntLit(i) =>
        IntLit(i)(pos)
      case p@PResultLit() =>
        // find function
        var par: Attributable = p.parent
        while (!par.isInstanceOf[PFunction]) {
          if (par == null) sys.error("cannot use 'result' outside of function")
          par = par.parent
        }
        Result()(ttyp(par.asInstanceOf[PFunction].typ), pos)
      case PBoolLit(b) =>
        if (b) TrueLit()(pos) else FalseLit()(pos)
      case PNullLit() =>
        NullLit()(pos)
      case PLocationAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos)
      case PFunctApp(func, args) =>
        members.get(func.name).get match {
          case f: Function => FuncApp(f, args map exp)(pos)
          case f@DomainFunc(name, formalArgs, typ) =>
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

            DomainFuncApp(f, actualArgs, map.toMap)(pos)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PUnfolding(loc, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos)
      case PExists(variable, e) =>
        Exists(liftVarDecl(variable), exp(e))(pos)
      case PForall(variable, e) =>
        Forall(liftVarDecl(variable), exp(e))(pos)
      case PCondExp(cond, thn, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos)
      case PCurPerm(loc) =>
        CurrentPerm(exp(loc).asInstanceOf[LocationAccess])(pos)
      case PNoPerm() =>
        NoPerm()(pos)
      case PFullPerm() =>
        FullPerm()(pos)
      case PWildcard() =>
        WildcardPerm()(pos)
      case PConcretePerm(a, b) =>
        ConcretePerm(a, b)(pos)
      case PEpsilon() =>
        EpsilonPerm()(pos)
      case PAccPred(loc, perm) =>
        val p = exp(perm)
        exp(loc) match {
          case loc@FieldAccess(rcv, field) =>
            FieldAccessPredicate(loc, p)(pos)
          case loc@PredicateAccess(rcv, pred) =>
            PredicateAccessPredicate(loc, p)(pos)
          case _ =>
            sys.error("unexpected location")
        }
      case PEmptySeq() =>
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
      case PSeqLength(seq) =>
        SeqLength(exp(seq))(pos)
    }
  }

  /** Takes a `scala.util.parsing.input.Position` and turns it into a `SourcePosition`. */
  implicit def liftPos(pos: scala.util.parsing.input.Position): SourcePosition = SourcePosition(pos.line, pos.column)

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVar`. */
  private def liftVarDecl(formal: PFormalArgDecl) = LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(formal.start)

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
    case PDomainType(name, args) =>
      members.get(name.name) match {
        case Some(d) =>
          val domain = d.asInstanceOf[Domain]
          val typVarMapping = domain.typVars zip (args map ttyp)
          DomainType(domain, (typVarMapping.filter {
            case (tv, tt) => !tt.isInstanceOf[TypeVar]
          }).toMap)
        case None =>
          assert(args.length == 0)
          TypeVar(name.name) // not a domain, i.e. it must be a type variable
      }
    case PUnkown() =>
      sys.error("unknown type unexpected here")
    case PPredicateType() =>
      sys.error("unexpected use of internal typ")
  }
}
