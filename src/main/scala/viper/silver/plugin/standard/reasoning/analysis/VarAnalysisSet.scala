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
    if (!(vars_outside_blk.intersect(all_tainted).isEmpty)) {
      val tainted_vars: Set[Declaration] = all_tainted.intersect(vars_outside_blk)
      val problem_vars: String = tainted_vars.mkString(", ")
      val problem_pos: String = tainted_vars.map(vs => vs.pos).mkString(", ")
      reportError(ConsistencyError("Universal introduction variable might have been assigned to variable " + problem_vars + " at positions (" + problem_pos + "), defined outside of the block", u.pos))
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
      case Seqn(ss, decls) => {
        for (s <- ss) {
          output = output ++ get_tainted_vars_stmt(output, s)
        }
        output
      }
      case LocalVarAssign(lhs, rhs) =>
        if (is_expr_tainted(tainted, rhs)) {
          tainted ++ Set(LocalVarDecl(lhs.name, lhs.typ)(stmt.pos))
        } else {
          tainted
        }

      case If(cond, thn, els) => {
        if (is_expr_tainted(tainted, cond)) {
          val written_vars_thn: Option[Set[LocalVarDecl]] = writtenTo(thn)
          val written_vars_els: Option[Set[LocalVarDecl]] = writtenTo(els)
          Set[Declaration]() ++ written_vars_thn.getOrElse(mutable.Set()) ++ written_vars_els.getOrElse(mutable.Set())
        } else {
          get_tainted_vars_stmt(tainted, thn) ++ get_tainted_vars_stmt(tainted, els)
        }
      }

      case w@While(cond, _, body) => {
        /*
        if (is_expr_tainted(tainted, cond)) {
          writtenTo(body).getOrElse(Set()) ++ Set[Declaration]()
        } else {
          get_tainted_vars_stmt(tainted, body)
        }
         */
        val new_tainted = get_tainted_vars_stmt(tainted, If(cond,body,Seqn(Seq(), Seq())(body.pos))(body.pos))
        if (new_tainted.equals(tainted)) {
          tainted
        } else {
          get_tainted_vars_stmt(new_tainted, w)
        }
      }

      case m@MethodCall(_, _, _) => {
        //Problem cannot reportError inside this trait!
        reportErrorWithMsg(ConsistencyError("Might be not allowed method call inside universal introduction block", m.pos))
        tainted // TODO: what needs to be returned here?
      }

      case i@Inhale(exp) => {
        if(exp.isPure) {
          tainted
        } else {
          reportErrorWithMsg(ConsistencyError("There might be an impure inhale expression inside universal introduction block", i.pos))
          tainted //What needs to be returned here
        }
      }

      case Assume(_) => {
        tainted
      }

      case Label(_, _) => {
        tainted
      }

      /** TODO: Do not allow Heap assignments */
      case f@FieldAssign(lhs, rhs) => {
        reportErrorWithMsg(ConsistencyError("FieldAssign for universal introduction block", f.pos))
        tainted // TODO: what needs to be returned here ?
      }

      case _ => {
        throw new UnsupportedOperationException("undefined statement for universal introduction block")
      }
    }
  }

  /*
  def checkStmt(tainted: mutable.Set[Declaration], stmt: Stmt, allTainted: Boolean) : mutable.Set[Declaration] = {
    stmt match {
      case Seqn(ss, _) => {
        for (s <- ss) {
          tainted ++= checkStmt(tainted, s, allTainted)
        }
        tainted
      }
      case LocalVarAssign(lhs, rhs) => {
        if (allTainted || checkExpr(tainted, rhs)) {
          tainted += LocalVarDecl(lhs.name, lhs.typ)(stmt.pos)
        }
        tainted
      }
      case If(cond, thn, els) => {
        if(checkExpr(tainted,cond)){
          val new_tainted: mutable.Set[Declaration] = checkStmt(tainted, thn, true)
          tainted ++= checkStmt(new_tainted, els,true)
        } else {
          val new_tainted: mutable.Set[Declaration] = checkStmt(tainted, thn, allTainted)
          tainted ++= checkStmt(new_tainted, els, allTainted)
        }
        tainted
      }

      case While(cond, _, body) => {
        if (checkExpr(tainted, cond)) {
          tainted ++= checkStmt(tainted, body, true)
        } else {
          tainted ++= checkStmt(tainted, body, allTainted)
        }
        tainted
      }

      case MethodCall(_, _, _) => {
        //Problem cannot reportError inside this trait!
        throw new IllegalArgumentException("Method call universal introduction")
      }

      case Inhale(exp) => {
        tainted ++= addExprToTainted(tainted, exp)
        tainted
      }

      case Assume(_) => {
        tainted
      }

      case Label(_, _) => {
        tainted
      }

      case _ => {
        throw new UnsupportedOperationException("undefined statement for universal introduction block")
      }
    }
  }

   */

  /**
    * expressions that should be added to tainted (e.g. for instance for inhale statements
    * @param tainted
    * @param exp
    * @return
    */
  def addExprToTainted(tainted: Set[Declaration], exp: Exp) : Set[Declaration] = {
    exp match {
      case l@LocalVar(_, _) => {
        tainted ++ Set(LocalVarDecl(l.name, l.typ)(exp.pos))
      }
      case BinExp(exp1, exp2) => {
        addExprToTainted(tainted, exp1) ++ addExprToTainted(tainted, exp2)
      }
      case UnExp(exp) => {
        addExprToTainted(tainted, exp)
      }
      case _ => tainted
    }
  }

  /**
    * check whether expression contains a tainted variable
    * @param tainted
    * @param exp
    * @return
    */
  def is_expr_tainted(tainted:Set[Declaration], exp:Exp) : Boolean = {
    exp match {
      case l@LocalVar(_, _) => {
        isTainted(LocalVarDecl(l.name, l.typ)(l.pos), tainted)
      }
      case BinExp(exp1, exp2) => {
        is_expr_tainted(tainted, exp1) || is_expr_tainted(tainted, exp2)
      }
      case UnExp(exp) => {
        is_expr_tainted(tainted, exp)
      }
      case _ => false
    }
  }

  def isTainted(name:Declaration, tainted:Set[Declaration]) : Boolean = {
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
      case Seqn(ss, _) => {
        for (s <- ss) {
          output match {
            case None => output = writtenTo(s)
            case Some(v) => output = Some(v ++ writtenTo(s).getOrElse(Set[LocalVarDecl]()))
          }

        }
        output
      }
      case LocalVarAssign(lhs, _) => {
        val lhs_var = LocalVarDecl(lhs.name, lhs.typ)(lhs.pos)
        Some(Set(lhs_var))
      }
      case If(_, thn, els) => {
        val writtenThn: Option[Set[LocalVarDecl]] = writtenTo(thn)
        val writtenEls: Option[Set[LocalVarDecl]] = writtenTo(els)
        (writtenThn, writtenEls) match {
          case (None,None) => None
          case (Some(_), None) => writtenThn
          case (None, Some(_)) => writtenEls
          case (Some(t), Some(e)) => Some(t++e)
        }
      }

      case While(_, _, body) => {
        writtenTo(body)
      }

      /** TODO */
      case MethodCall(_, _, _) => {
        None
      }


      case Inhale(_) => {
        None
      }

      case Assume(_) => {
        None
      }

      case Label(_, _) => {
        None
      }

      case _ => {
        None
      }
    }
  }

  /*

  /**
    * check that universal introduction variables aren't changed.
    * True if immutable variables are reassigned false otherwise
    */

  // change this so it is called written (or writtenTo)
  // writtenTo(stmt:Stmt) : optionalSet[LocalVarDecl] {}
  def check_is_reassigned(vars: Seq[LocalVarDecl], stmt: Stmt): Seq[LocalVarDecl] = {
    var output = Seq[LocalVarDecl]()
    stmt match {
      case Seqn(ss, _) => {
        for (s <- ss) {
          output = output ++ check_is_reassigned(vars, s)
        }
        output
      }
      case LocalVarAssign(lhs, _) => {
        var output = Seq[LocalVarDecl]()
        val lhs_var = LocalVarDecl(lhs.name, lhs.typ)(lhs.pos)
        if (vars.contains(lhs_var)) {
          output ++= Seq(lhs_var)
        }
        output
      }
      case If(_, thn, els) => {
        check_is_reassigned(vars, thn) ++ check_is_reassigned(vars, els)
      }

      case While(_, _, body) => {
        check_is_reassigned(vars, body)
      }

      /** return false for now if immutable vars are part of arguments of method call */
      case MethodCall(_, args, _) => {
        var output = Seq[LocalVarDecl]()
        for (exp <- args) {
          output = output ++ expr_contains_immutable(vars, exp)
        }
        output
      }


      case Inhale(_) => {
        Seq[LocalVarDecl]()
      }

      case Assume(_) => {
        Seq[LocalVarDecl]()
      }

      case Label(_, _) => {
        Seq[LocalVarDecl]()
      }

      case _ => {
        Seq[LocalVarDecl]()
      }
    }
  }

  def expr_contains_immutable(vars: Seq[LocalVarDecl], exp: Exp): Seq[LocalVarDecl] = {
    exp match {
      case l@LocalVar(_, _) => {
        val v = LocalVarDecl(l.name, l.typ)(l.pos)
        if(vars.contains(v)){
          Seq(v)
        } else {
          Seq()
        }
      }
      case BinExp(exp1, exp2) => {
        expr_contains_immutable(vars, exp1) ++ expr_contains_immutable(vars, exp2)
      }
      case UnExp(exp) => {
        expr_contains_immutable(vars, exp)
      }
      case _ => Seq()
    }
  }

   */

  /*

  def check_is_reassigned_bool(vars: Seq[LocalVarDecl], stmt: Stmt) : Boolean = {
    var output = false
    stmt match {
      case Seqn(ss, _) => {
        for (s <- ss) {
          output = check_is_reassigned(vars, s)
        }
        output
      }
      case LocalVarAssign(lhs, _) => {
        var output: Boolean = false
        if (vars.contains(LocalVarDecl(lhs.name, lhs.typ)(lhs.pos))) {
          output = true
        }
        output
      }
      case If(_, thn, els) => {
        check_is_reassigned(vars, thn) || check_is_reassigned(vars, els)
      }

      case While(_, _, body) => {
        check_is_reassigned(vars, body)
      }

      /** return false for now if immutable vars are part of arguments of method call */
      case MethodCall(_, args, _) => {
        var output: Boolean = false
        for (exp <- args) {
          output = output || expr_contains_immutable(vars, exp)
        }
        output
      }


      case Inhale(_) => {
        false
      }

      case Assume(_) => {
        false
      }

      case Label(_, _) => {
        false
      }

      case _ => {
        false
      }
    }
  }

  def expr_contains_immutable_bool(vars: Seq[LocalVarDecl], exp: Exp): Boolean = {
    exp match {
      case l@LocalVar(_, _) => {
        vars.contains(LocalVarDecl(l.name, l.typ)(l.pos))
      }
      case BinExp(exp1, exp2) => {
        expr_contains_immutable(vars, exp1) || expr_contains_immutable(vars, exp2)
      }
      case UnExp(exp) => {
        expr_contains_immutable(vars, exp)
      }
      case _ => false
    }
  }*/
}
