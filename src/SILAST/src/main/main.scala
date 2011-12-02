package main

import silAST.expressions._
import terms._

object Main {

  def main(args: Array[String]) {
    println("Hiho")
  }

  def f(e : Expression)
  {
    e match {
      case AccessPermissionExpression(_,_,_) => 0
      case UnfoldingExpression(_,_,_) => 1
      case EqualityExpression(_,_,_) => 2
      case UnaryBooleanExpression(_,_,_) => 3
      case BinaryBooleanExpression(_,_,_,_) => 4
      case DomainPredicateExpression(_,_,_) => 5
      case PredicateExpression(_,_,_) => 6
      case QuantifierExpression(_,_,_,_) => 7
    }
  }
  def f2(e : Expression)
  {
    e match {
      case AccessPermissionExpression(_,_,_) => 0
      case UnfoldingExpression(_,_,_) => 1
      case EqualityExpression(_,_,_) => 2
      case UnaryBooleanExpression(_,_,_) => 3
      case BinaryBooleanExpression(_,_,_,_) => 4
      case DomainPredicateExpression(_,_,_) => 5
      case PredicateExpression(_,_,_) => 6
//      case QuantifierExpression(_,_,_,_) => 7
    }
  }

  def g(t : Term)
  {
    t match {
      case LiteralTerm(_) => 1

      case BoundVariableTerm(_,_) => 1
      case FunctionApplicationTerm(_,_,_,_) => 3
      case DomainFunctionApplicationTerm(_,_,_) => 3

      case ProgramVariableTerm(_,_) => 2
      case CastTerm(_,_,_) => 2
      case FieldReadTerm(_,_,_) => 6
      case OldFieldReadTerm(_,_,_) => 6
    }

    t match {
      case LiteralTerm(_) => 1

      case BoundVariableTerm(_,_) => 1
      case FunctionApplicationTerm(_,_,_,_) => 3
//      case DomainFunctionApplicationTerm(_,_,_) => 3

      case ProgramVariableTerm(_,_) => 2
      case CastTerm(_,_,_) => 2
      case FieldReadTerm(_,_,_) => 6
      case OldFieldReadTerm(_,_,_) => 6
    }
  }

/*
  def g2(e : ProgramExpression)
  {
    e match {
      case PEqualityExpression(_,_,_) => 2
      case PUnaryBooleanExpression(_,_,_) => 3
      case PBinaryBooleanExpression(_,_,_,_) => 4
      case PDomainPredicateExpression(_,_,_) => 5
      case PPredicateExpression(_,_,_) => 6
    }
  }

  def g2(e : ProgramExpression)
  {
    e match {
      case PEqualityExpression(_,_,_) => 2
      case PUnaryBooleanExpression(_,_,_) => 3
      case PBinaryBooleanExpression(_,_,_,_) => 4
      case PDomainPredicateExpression(_,_,_) => 5
//      case PPredicateExpression(_,_,_) => 6
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