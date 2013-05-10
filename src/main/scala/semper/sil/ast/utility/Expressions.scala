package semper.sil.ast.utility

import semper.sil.ast._
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import scala.Some
import semper.sil.ast.Unfolding
import semper.sil.ast.LocalVarDecl
import semper.sil.ast.CondExp
import semper.sil.ast.IntLit
import semper.sil.ast.NullLit
import semper.sil.ast.DomainFuncApp
import scala.Some
import semper.sil.ast.FuncApp

/** Utility methods for expressions. */
object Expressions {
  def isPure(e: Exp): Boolean = e match {
    case _: AccessPredicate => false

    case UnExp(e0) => isPure(e0)
    case InhaleExhaleExp(in, ex) => isPure(in) && isPure(ex)
    case BinExp(e0, e1) => isPure(e0) && isPure(e1)
    case CondExp(cnd, thn, els) => isPure(cnd) && isPure(thn) && isPure(els)
    case Unfolding(_, in) => isPure(in) /* Assuming that the first argument is pure */
    case QuantifiedExp(_, e0) => isPure(e0)

    case  _: Literal
        | _: PermExp
        | _: FuncApp
        | _: DomainFuncApp
        | _: LocationAccess
        | _: AbstractLocalVar
        | _: SeqExp
    => true
  }

  def whenInhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(in, _) => in
  })

  def whenExhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(_, ex) => ex
  })

  /**
   * In an expression, instantiate a list of variables with given expressions.
   */
  def instantiateVariables(exp: Exp, variables: Seq[LocalVarDecl], values: Seq[Exp]): Exp = {
    val argNames = (variables map (_.name)).zipWithIndex
    def actualArg(formalArg: String): Option[Exp] = {
      argNames.find(x => x._1 == formalArg) map {
        case (_, idx) => values(idx)
      }
    }
    exp.transform {
      case LocalVar(name) if actualArg(name).isDefined => actualArg(name).get
    }()
  }

  def subExps(e: Exp) = e.subnodes collect { case e: Exp => e }

}
