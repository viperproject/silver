/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._

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
          case NewStmt(target, fields) => Seq(target) ++ fields
          case LocalVarAssign(lhs, rhs) => Seq(lhs, rhs)
          case FieldAssign(lhs, rhs) => Seq(lhs, rhs)
          case Fold(e) => Seq(e)
          case Unfold(e) => Seq(e)
          case Package(e) => Seq(e)
          case Apply(e) => Seq(e)
          case Inhale(e) => Seq(e)
          case Exhale(e) => Seq(e)
          case Assert(e) => Seq(e)
          case MethodCall(mname, args, targets) => args ++ targets
          case Seqn(ss) => ss
          case While(cond, invs, locals, body) => Seq(cond) ++ invs ++ locals ++ Seq(body)
          case If(cond, thn, els) => Seq(cond, thn, els)
          case Label(name) => Nil
          case Goto(target) => Nil
          case Fresh(vars) => vars
          case Constraining(vars, body) => vars ++ Seq(body)
        }
      case vd: LocalVarDecl => Nil
      case e: Exp =>
        // Note: If you have to update this pattern match to make it exhaustive, it
        // might also be necessary to update the PrettyPrinter.toParenDoc method.
        e match {
          case _: Literal => Nil
          case _: AbstractLocalVar => Nil
          case FieldAccess(rcv, field) => Seq(rcv)
          case PredicateAccess(params, _) => params
          case e: UnFoldingExp => Seq(e.acc, e.body)
          case Applying(wand, in) => Seq(wand, in)
          case Packaging(wand, in) => Seq(wand, in)
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
          case FuncApp(_, args) => args
          case DomainFuncApp(_, args, m) =>
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
        }
      case t: Type => Nil
    }
    n match {
      case t: Typed => subnodesWithType ++ Seq(t.typ)
      case _ => subnodesWithType
    }
  }

  def children(node: Node): (Seq[Node], Seq[Any]) = {
    val relevantChildren = node match {
      case p: Product => p.productIterator.toSeq
    }

    relevantChildren.partition(_.isInstanceOf[Node])
                    .asInstanceOf[(Seq[Node], Seq[Any])]
  }
}




