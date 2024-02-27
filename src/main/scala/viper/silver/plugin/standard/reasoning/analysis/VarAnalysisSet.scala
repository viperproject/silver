package viper.silver.plugin.standard.reasoning.analysis

import viper.silver.ast.{Assume, BinExp, Declaration, Exp, FieldAssign, If, Inhale, Label, LocalVar, LocalVarAssign, LocalVarDecl, MethodCall, Seqn, Stmt, UnExp, While}
import viper.silver.plugin.standard.reasoning.UniversalIntro
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable

trait VarAnalysisSet {

  def reportErrorWithMsg(error: AbstractError): Unit


  def executeTaintedSetAnalysis(tainted: Set[Declaration], vars_outside_blk: mutable.Set[Declaration], blk: Seqn, u: UniversalIntro, reportError: AbstractError => Unit): Unit = {
    /** check whether any additional variables are tainted inside of the block */
    var all_tainted = Set[Declaration]()
    all_tainted = get_tainted_vars_stmt(tainted, blk)


    /** remove the variables that were tainted to begin with */
    vars_outside_blk --= mutable.Set(u.transitiveScopedDecls: _*)

    /** check whether any variables were tainted that are declared outside of our block */
    if (vars_outside_blk.intersect(all_tainted).nonEmpty) {
      val tainted_vars: Set[Declaration] = all_tainted.intersect(vars_outside_blk)
      val problem_vars: String = tainted_vars.mkString(", ")
      reportError(ConsistencyError(s"Universal introduction variable might have been assigned to variable $problem_vars, defined outside of the block", u.pos))
    }
  }

  /**
    * check which arguments are influenced by universal introduction variables and add them to the tainted set.
    * @param tainted
    * @param stmt
    * @return
    */
  def get_tainted_vars_stmt(tainted: Set[Declaration], stmt: Stmt): Set[Declaration] = {
    var output: Set[Declaration] = tainted
    stmt match {
      case Seqn(ss, _) =>
        for (s <- ss) {
          output = get_tainted_vars_stmt(output, s)
        }
        output
      case LocalVarAssign(lhs, rhs) =>
        if (is_expr_tainted(tainted, rhs)) {
          tainted ++ Set(LocalVarDecl(lhs.name, lhs.typ)(stmt.pos))
        } else {
          tainted -- Set(LocalVarDecl(lhs.name, lhs.typ)(stmt.pos))
        }

      case If(cond, thn, els) =>
        if (is_expr_tainted(tainted, cond)) {
          val written_vars_thn = writtenTo(thn)
          val written_vars_els = writtenTo(els)
          Set[Declaration]() ++ written_vars_thn.getOrElse(mutable.Set()) ++ written_vars_els.getOrElse(mutable.Set())
        } else {
          get_tainted_vars_stmt(tainted, thn) ++ get_tainted_vars_stmt(tainted, els)
        }

      case w@While(cond, _, body) =>
        val new_tainted = get_tainted_vars_stmt(tainted, If(cond,body,Seqn(Seq(), Seq())(body.pos))(body.pos))
        if (new_tainted.equals(tainted)) {
          tainted
        } else {
          get_tainted_vars_stmt(new_tainted, w)
        }

      case m@MethodCall(_, _, _) =>
        reportErrorWithMsg(ConsistencyError("Might be not allowed method call inside universal introduction block", m.pos))
        tainted

      case i@Inhale(exp) =>
        if(exp.isPure) {
          tainted
        } else {
          reportErrorWithMsg(ConsistencyError("There might be an impure inhale expression inside universal introduction block", i.pos))
          tainted
        }

      case Assume(_) => tainted

      case Label(_, _) => tainted

      /** TODO: Do not allow Heap assignments */
      case f@FieldAssign(_, _) =>
        reportErrorWithMsg(ConsistencyError("FieldAssign for modular flow analysis with sets", f.pos))
        tainted

      case s@_ =>
        reportErrorWithMsg(ConsistencyError("undefined statement for modular flow analysis with set", s.pos))
        tainted
    }
  }


  /**
    * expressions that should be added to tainted (e.g. for instance for inhale statements
    * @param tainted
    * @param exp
    * @return
    */
  private def addExprToTainted(tainted: Set[Declaration], exp: Exp) : Set[Declaration] = {
    exp match {
      case l@LocalVar(_, _) => tainted ++ Set(LocalVarDecl(l.name, l.typ)(exp.pos))
      case BinExp(exp1, exp2) => addExprToTainted(tainted, exp1) ++ addExprToTainted(tainted, exp2)
      case UnExp(exp) => addExprToTainted(tainted, exp)
      case _ => tainted
    }
  }

  /**
    * check whether expression contains a tainted variable
    * @param tainted
    * @param exp
    * @return
    */
  private def is_expr_tainted(tainted:Set[Declaration], exp:Exp) : Boolean = {
    exp match {
      case l@LocalVar(_, _) => isTainted(LocalVarDecl(l.name, l.typ)(l.pos), tainted)
      case BinExp(exp1, exp2) => is_expr_tainted(tainted, exp1) || is_expr_tainted(tainted, exp2)
      case UnExp(exp) => is_expr_tainted(tainted, exp)
      case _ => false
    }
  }

  private def isTainted(name:Declaration, tainted:Set[Declaration]): Boolean = {
    tainted.contains(name)
  }

  /**
    * return variables that are assigned new values
    * @param stmt
    * @return
    */
  def writtenTo(stmt: Stmt): Option[Set[LocalVarDecl]] = {
    var output: Option[Set[LocalVarDecl]] = None
    stmt match {
      case Seqn(ss, _) =>
        for (s <- ss) {
          output match {
            case None => output = writtenTo(s)
            case Some(v) => output = Some(v ++ writtenTo(s).getOrElse(Set[LocalVarDecl]()))
          }
        }
        output

      case LocalVarAssign(lhs, _) =>
        val lhs_var = LocalVarDecl(lhs.name, lhs.typ)(lhs.pos)
        Some(Set(lhs_var))

      case If(_, thn, els) =>
        val writtenThn = writtenTo(thn)
        val writtenEls = writtenTo(els)
        (writtenThn, writtenEls) match {
          case (None,None) => None
          case (Some(_), None) => writtenThn
          case (None, Some(_)) => writtenEls
          case (Some(t), Some(e)) => Some(t++e)
        }

      case While(_, _, body) => writtenTo(body)

      /** TODO */
      case MethodCall(_, _, _) => None
      case Inhale(_) => None
      case Assume(_) => None
      case Label(_, _) => None
      case _ => None
    }
  }
}
