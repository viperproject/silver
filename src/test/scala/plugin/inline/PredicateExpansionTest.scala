package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.plugin.standard.inline.PredicateExpansion

class PredicateExpansionTest extends FunSuite with PredicateExpansion {

  test("propagatePermission should evaluate to None if the body of the predicate is None") {
    val maybePredBody = None
    val perm = FullPerm()()

    propagatePermission(maybePredBody, perm).isEmpty
  }

  test("propagatePermission should propagate a fractional permission to one access") {
    // Something like: acc(x.f, write), replace with acc(this.left, 1/2)
    val fieldAccess = FieldAccessPredicate(
      FieldAccess(LocalVar("x", Ref)(),Field("f",Int)(NoPosition))(NoPosition), FullPerm()(NoPosition)
    )(NoPosition)
    val maybePredBody = Some(fieldAccess)
    val permToChangeTo = FractionalPerm(IntLit(1)(), IntLit(2)())()

    propagatePermission(maybePredBody, permToChangeTo).exists {
      case FieldAccessPredicate(_, changedPerm) => changedPerm == permToChangeTo
      case _ => false
    }
  }

  test("propagatePermission should propagate a fractional permission to more than one access") {
    // Something like: acc(x.left, write) && acc(x.right, write)
    val leftAccess = FieldAccessPredicate(
      FieldAccess(LocalVar("x", Ref)(),Field("left",Int)(NoPosition))(NoPosition), FullPerm()(NoPosition)
    )(NoPosition)
    val rightAccess = FieldAccessPredicate(
      FieldAccess(LocalVar("x", Ref)(),Field("right",Int)(NoPosition))(NoPosition), FullPerm()(NoPosition)
    )(NoPosition)
    val maybePredBody = Some(And(leftAccess, rightAccess)())
    val permToChangeTo = FractionalPerm(IntLit(1)(), IntLit(2)())()

    propagatePermission(maybePredBody, permToChangeTo).exists {
      case FieldAccessPredicate(FieldAccess(LocalVar(_, _), Field("left", _)), changedPerm) =>
        changedPerm == permToChangeTo
      case FieldAccessPredicate(FieldAccess(LocalVar(_, _), Field("right", _)), changedPerm) =>
        changedPerm == permToChangeTo
      case _ => false
    }
  }
}
