package semper.sil.ast.utility

import scala.collection.immutable.ListSet
import semper.sil.ast._

/** Utility methods for AST nodes. */
object Nodes {

  /**
   * See Node.subnodes.
   */
  def subnodes(n: Node): Seq[Node] = {
    val subnodesWithType = n match {
      case Trigger(exps) => exps
      case Program(domains, fields, functions, predicates, methods) =>
        domains ++ fields ++ functions ++ predicates ++ methods
      case m: Member =>
        m match {
          case Field(name, typ) => Nil
          case Function(name, formalArgs, typ, pres, posts, exp) =>
            formalArgs ++ pres ++ posts ++ Seq(exp)
          case Method(name, formalArgs, formalReturns, pres, posts, locals, body) =>
            formalArgs ++ formalReturns ++ pres ++ posts ++ locals ++ Seq(body)
          case Predicate(name, formalArg, body) => Seq(body)
          case Domain(name, functions, axioms, typVars) =>
            functions ++ axioms ++ typVars
        }
      case dm: DomainMember =>
        dm match {
          case DomainAxiom(_, exp) => Seq(exp)
          case DomainFunc(_, formalArgs, _, _) => formalArgs
        }
      case s: Stmt =>
        s match {
          case NewStmt(lhs) => Seq(lhs)
          case LocalVarAssign(lhs, rhs) => Seq(lhs, rhs)
          case FieldAssign(lhs, rhs) => Seq(lhs, rhs)
          case Fold(e) => Seq(e)
          case Unfold(e) => Seq(e)
          case Inhale(e) => Seq(e)
          case Exhale(e) => Seq(e)
          case Assert(e) => Seq(e)
          case MethodCall(m, args, targets) => args ++ targets
          case Seqn(ss) => ss
          case While(cond, invs, locals, body) => Seq(cond) ++ invs ++ locals ++ Seq(body)
          case If(cond, thn, els) => Seq(cond, thn, els)
          case Label(name) => Nil
          case Goto(target) => Nil
          case FreshReadPerm(vars, body) => vars ++ Seq(body)
        }
      case vd: LocalVarDecl => Nil
      case e: Exp =>
        // Note: If you have to update this pattern match to make it exhaustive, it
        // might also be necessary to update the PrettyPrinter.toParenDoc method.
        e match {
          case _: Literal => Nil
          case AbstractLocalVar(n) => Nil
          case FieldAccess(rcv, field) => Seq(rcv)
          case PredicateAccess(rcv, predicate) => Seq(rcv)
          case Unfolding(acc, exp) => Seq(acc, exp)
          case Old(exp) => Seq(exp)
          case CondExp(cond, thn, els) => Seq(cond, thn, els)
          case Exists(v, exp) => v ++ Seq(exp)
          case Forall(v, triggers, exp) => v ++ triggers ++ Seq(exp)
          case InhaleExhaleExp(in, ex) => Seq(in, ex)
          case WildcardPerm() => Nil
          case FullPerm() => Nil
          case NoPerm() => Nil
          case EpsilonPerm() => Nil
          case CurrentPerm(loc) => Seq(loc)
          case FractionalPerm(left, right) => Seq(left, right)
          case AccessPredicate(loc, perm) => Seq(loc, perm)
          case BinExp(left, right) => Seq(left, right)
          case UnExp(exp) => Seq(exp)
          case FuncApp(func, args) => args
          case DomainFuncApp(func, args, m) =>
            args ++ m.keys ++ m.values

          case EmptySeq(elemTyp) => Seq(elemTyp)
          case ExplicitSeq(elems) => elems
          case RangeSeq(low, high) => Seq(low, high)
          case SeqAppend(left, right) => Seq(left, right)
          case SeqIndex(seq, idx) => Seq(seq, idx)
          case SeqTake(seq, nn) => Seq(seq, nn)
          case SeqDrop(seq, nn) => Seq(seq, nn)
          case SeqContains(elem, seq) => Seq(elem, seq)
          case SeqUpdate(seq, idx, elem) => Seq(seq, idx, elem)
          case SeqLength(seq) => Seq(seq)

          case EmptySet(elemTyp) => Seq(elemTyp)
          case ExplicitSet(elems) => elems
          case EmptyMultiset(elemTyp) => Seq(elemTyp)
          case ExplicitMultiset(elems) => elems
          case AnySetUnion(left, right) => Seq(left, right)
          case AnySetIntersection(left, right) => Seq(left, right)
          case AnySetSubset(left, right) => Seq(left, right)
          case AnySetContains(elem, s) => Seq(elem, s)
          case AnySetCardinality(s) => Seq(s)
        }
      case t: Type => Nil
    }
    n match {
      case t: Typed => subnodesWithType ++ Seq(t.typ)
      case _ => subnodesWithType
    }
  }
}




