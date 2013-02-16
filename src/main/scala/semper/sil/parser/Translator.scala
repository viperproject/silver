package semper.sil.parser

import semper.sil.ast._
import utility.Statements

/**
 * Takes an abstract syntax tree after parsing is done and translates it into a SIL abstract
 * syntax tree.
 *
 * Note that the translator assumes that the tree is well-formed (it typechecks and follows all the rules
 * of a valid SIL program).  No checks are performed, and the code might crash if the input is malformed.
 */
object Translator {

  def translate(pnode: PNode): Node = {
    pnode match {
      case e: PExp => exp(e)
      case s: PStmt => stmt(s)
      case _: PFormalArgDecl | _: PIdnDef | _: PType => sys.error("unexpected node")
      case PMethod(name, formalArgs, formalReturns, pres, posts, body) =>
        val plocals = body.childStmts collect { case l: PLocalVarDecl => l }
        val locals = plocals map {
          case p@PLocalVarDecl(idndef, t, _) => LocalVar(idndef.name)(typ(t), p.start)
        }
        Method(name.name, formalArgs map liftVarDecl, formalReturns map liftVarDecl, pres map exp, posts map exp, locals, stmt(body))()
    }
  }

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  def stmt(s: PStmt): Stmt = {
    val pos = s.start
    s match {
      case PVarAssign(idndef, rhs) =>
        LocalVarAssign(LocalVar(idndef.name)(Int, pos), exp(rhs))(pos) // TODO correct type
      case PLocalVarDecl(idndef, t, Some(init)) =>
        LocalVarAssign(LocalVar(idndef.name)(typ(t), pos), exp(init))(pos)
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
      case PIf(cond, thn, els) =>
        If(exp(cond), stmt(thn), stmt(els))(pos)
      case PWhile(cond, invs, body) =>
        While(exp(cond), invs map exp, stmt(body))(pos)
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(pexp: PExp): Exp = {
    val pos = pexp.start
    pexp match {
      case PIdnUse(name) => LocalVar(name)(Int, pos) // TODO correct typ and consider fields
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
          case "<==>" => Equiv(l, r)(pos)
          case "&&" => And(l, r)(pos)
          case "||" => Or(l, r)(pos)
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op match {
          case "+" => e
          case "-" => Neg(e)(pos)
        }
      case PIntLit(i) => IntLit(i)(pos)
      case PThisLit() => ThisLit()(pos)
      case PResultLit() => Result()(Int, pos) // TODO correct typ
      case PBoolLit(b) => if (b) TrueLit()(pos) else FalseLit()(pos)
      case PFieldAcc(rcv, idn) => FieldAccess(exp(rcv), null)(pos) // correct field
    }
  }

  /** Takes a `scala.util.parsing.input.Position` and turns it into a `SourcePosition`. */
  implicit def liftPos(pos: scala.util.parsing.input.Position): SourcePosition = SourcePosition(pos.line, pos.column)

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVar`. */
  def liftVarDecl(formal: PFormalArgDecl) = LocalVar(formal.idndef.name)(typ(formal.typ))

  /** Takes a `PType` and turns it into a `Type`. */
  def typ(t: PType) = t match {
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
