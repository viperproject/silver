package main

import silAST.expressions._

object Main {

  def main(args: Array[String]) {
    println("Hiho")
  }

  def f(e : Expression)
  {
    e match {
      case AccessPermissionExpression(_,_) => 0
      case UnfoldingExpression(_,_) => 1
      case EqualityExpression(_,_) => 2
      case UnaryBooleanExpression(_,_) => 3
      case BinaryBooleanExpression(_,_,_) => 4
      case DomainPredicateExpression(_,_) => 5
      case PredicateExpression(_,_) => 6
      case QuantifierExpression(_,_,_) => 7
    }
  }
         /*
  def g(e : ProgramExpression)
  {
    e match {
      case PEqualityExpression(_,_) => 2
      case PUnaryBooleanExpression(_,_) => 3
      case PBinaryBooleanExpression(_,_,_) => 4
      case PDomainPredicateExpression(_,_) => 5
//      case PPredicateExpression(_,_) => 6
    }
  }

  def g(e : DomainExpression)
  {
    e match {
      case DEqualityExpression(_,_) => 2
      case DUnaryBooleanExpression(_,_) => 3
      case DBinaryBooleanExpression(_,_,_) => 4
      case DDomainPredicateExpression(_,_) => 5
//      case DQuantifierExpression(_,_,_) => 5
    }
  }
 */
}