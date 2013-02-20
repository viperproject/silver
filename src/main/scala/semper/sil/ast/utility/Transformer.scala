package semper.sil.ast.utility

import semper.sil.ast._

/**
 * An implementation for transformers of the SIL AST.
 *
 * @author Stefan Heule
 */
object Transformer {

  /**
   * See Exp.transform.
   */
  def transform(exp: Exp, f: Exp => Option[Exp]): Exp = {
    val p = exp.pos
    val i = exp.info
    val func = (e: Exp) => transform(e, f)
    val t = f(exp)
    t match {
      case Some(ee) => ee
      case None =>
        exp match {
          case IntLit(_) => exp
          case BoolLit(_) => exp
          case AbstractLocalVar(_) => exp
          case FieldAccess(rcv, field) => FieldAccess(func(rcv), field)(p, i)
          case PredicateAccess(rcv, predicate) => PredicateAccess(func(rcv), predicate)(p, i)
          case Unfolding(acc, e) => Unfolding(func(acc).asInstanceOf[PredicateAccessPredicate], func(e))(p, i)
          case Old(e) => Old(func(e))(p, i)
          case CondExp(cond, thn, els) => CondExp(func(cond), func(thn), func(els))(p, i)
          case Exists(v, e) => Exists(v, func(e))(p, i)
          case Forall(v, e) => Forall(v, func(e))(p, i)
          case ReadPerm() => exp
          case FullPerm() => exp
          case NoPerm() => exp
          case EpsilonPerm() => exp
          case CurrentPerm(loc) => CurrentPerm(func(loc).asInstanceOf[LocationAccess])(p, i)
          case ConcretePerm(a, b) => exp
          case FieldAccessPredicate(loc, perm) =>
            FieldAccessPredicate(func(loc).asInstanceOf[FieldAccess], func(perm))(p, i)
          case PredicateAccessPredicate(loc, perm) =>
            PredicateAccessPredicate(func(loc).asInstanceOf[PredicateAccess], func(perm))(p, i)
          case FuncApp(ff, rcv, args) => FuncApp(ff, func(rcv), args map func)(p, i)
          case DomainFuncApp(ff, args) => DomainFuncApp(ff, args map func)(p, i)

          case Neg(e) => Neg(func(e))(p, i)
          case Not(e) => Not(func(e))(p, i)

          case Or(l, r) => Or(func(l), func(r))(p, i)
          case And(l, r) => And(func(l), func(r))(p, i)
          case Implies(l, r) => Implies(func(l), func(r))(p, i)

          case Add(l, r) => Add(func(l), func(r))(p, i)
          case Sub(l, r) => Sub(func(l), func(r))(p, i)
          case Mul(l, r) => Mul(func(l), func(r))(p, i)
          case Div(l, r) => Div(func(l), func(r))(p, i)
          case Mod(l, r) => Mod(func(l), func(r))(p, i)

          case LtCmp(l, r) => LtCmp(func(l), func(r))(p, i)
          case LeCmp(l, r) => LeCmp(func(l), func(r))(p, i)
          case GtCmp(l, r) => GtCmp(func(l), func(r))(p, i)
          case GeCmp(l, r) => GeCmp(func(l), func(r))(p, i)

          case EqCmp(l, r) => EqCmp(func(l), func(r))(p, i)
          case NeCmp(l, r) => NeCmp(func(l), func(r))(p, i)

          case PermAdd(l, r) => PermAdd(func(l), func(r))(p, i)
          case PermSub(l, r) => PermSub(func(l), func(r))(p, i)
          case PermMul(l, r) => PermMul(func(l), func(r))(p, i)
          case PermIntMul(l, r) => PermIntMul(func(l), func(r))(p, i)

          case PermLtCmp(l, r) => PermLtCmp(func(l), func(r))(p, i)
          case PermLeCmp(l, r) => PermLeCmp(func(l), func(r))(p, i)
          case PermGtCmp(l, r) => PermGtCmp(func(l), func(r))(p, i)
          case PermGeCmp(l, r) => PermGeCmp(func(l), func(r))(p, i)
        }
    }
  }
}
