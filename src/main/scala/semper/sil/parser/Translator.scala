package semper.sil.parser

import semper.sil.ast._
import utility.Statements
import language.implicitConversions

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
      case PProgram(name, domains, fields, functions, predicates, methods) =>
        (domains ++ fields ++ functions ++ predicates ++ methods) map translateMemberSignature
        val f = fields map (translate(_))
        val fs = functions map (translate(_))
        val p = predicates map (translate(_))
        val m = methods map (translate(_))
        Program(name.name, Nil, f, fs, p, m)(program.start)
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

  private val members = collection.mutable.HashMap[String, Member]()
  /**
   * Translate the signature of a member, so that it can be looked up later.
   */
  private def translateMemberSignature(p: PMember) {
    val pos = p.start
    val name = p.idndef.name
    val t: Member = p match {
      case PField(_, typ) =>
        Field(name, ttyp(typ))(pos)
      case PFunction(_, formalArgs, typ, _, _, _) =>
        Function(name, formalArgs map liftVarDecl, ttyp(typ), null, null, null)(pos)
      case PDomain(name, typVars, funcs, axioms) => ???
      case PPredicate(_, formalArg, _) =>
        Predicate(name, liftVarDecl(formalArg), null)(pos)
      case PMethod(_, formalArgs, formalReturns, _, _, _) =>
        Method(name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, null, null, null, null)(pos)
    }
    members.put(p.idndef.name, t)
  }

  private def findDomain(id: Identifier) = members.get(id.name).get.asInstanceOf[Domain]
  private def findField(id: Identifier) = members.get(id.name).get.asInstanceOf[Field]
  private def findFunction(id: Identifier) = members.get(id.name).get.asInstanceOf[Function]
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
      case PResultLit() =>
        Result()(Int, pos) // TODO correct typ
      case PBoolLit(b) =>
        if (b) TrueLit()(pos) else FalseLit()(pos)
      case PNullLit() =>
        NullLit()(pos)
      case PLocationAccess(rcv, idn) =>
        FieldAccess(exp(rcv), findField(idn))(pos)
      case PFunctApp(func, args) => ???
      case PUnfolding(loc, exp) => ???
      case PExists(variable, exp) => ???
      case PForall(variable, exp) => ???
      case PCondExp(cond, thn, els) => ???
      case PCurPerm(loc) => ???
      case PNoPerm() => ???
      case PWildcard() => ???
      case PConcretePerm(a, b) => ???
      case PEpsilon() => ???
      case PAccPred(loc, perm) => ???
    }
  }

  /** Takes a `scala.util.parsing.input.Position` and turns it into a `SourcePosition`. */
  implicit def liftPos(pos: scala.util.parsing.input.Position): SourcePosition = SourcePosition(pos.line, pos.column)

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVar`. */
  private def liftVarDecl(formal: PFormalArgDecl) = LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(formal.start)

  /** Takes a `PType` and turns it into a `Type`. */
  private def ttyp(t: PType) = t match {
    case PPrimitiv(name) => name match {
      case "Int" => Int
      case "Bool" => Bool
      case "Ref" => Ref
      case "Perm" => Perm
    }
    case PTypeVar(n) => TypeVar(n)
    case PDomainType(domain, args) => Int // TODO
    case PUnkown() => sys.error("unknown type unexpected here")
  }
}
