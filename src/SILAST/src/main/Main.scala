package main

import silAST.expressions._
import terms._
import silAST.programs.ProgramFactory
import silAST.symbols.logical.{ImplicationOperator,Not}
import silAST.symbols.logical.quantification.Forall
import silAST.source.noLocation

object Main {

  def main(args: Array[String]) {
    println("Hiho")
    makeProgram()
  }

  def makeProgram() = {
    val nl = noLocation

    val pf = new ProgramFactory("P1")

    val id = pf.getDomainFactory("Integer");
    val integerType = pf.makeNonReferenceDataType(nl,id)
    val isd = pf.getDomainFactory("IntegerSeq");
    val integerSeqType = pf.makeNonReferenceDataType(nl,isd);
    {
      val sigTail = isd.defineDomainFunctionSignature(nl,isd.makeDataTypeSequence(List(integerSeqType)),integerSeqType)
      val tail = isd.defineDomainFunction(nl,"tail",sigTail)
      val sigPrepend = isd.defineDomainFunctionSignature(nl,isd.makeDataTypeSequence(List(integerType,integerSeqType)),integerSeqType)
      val prepend = isd.defineDomainFunction(nl,"prepend",sigPrepend)
      val sigP = isd.defineDomainPredicateSignature(nl,isd.makeDataTypeSequence(List(integerSeqType)))
      val isEmpty = isd.defineDomainPredicate(nl,"isEmpty",sigP)

      val varX = isd.makeBoundVariable(nl,"x",integerSeqType)
      val varE = isd.makeBoundVariable(nl,"y",integerType)
      val xT = isd.makeBoundVariableTerm(nl,varX)
      val eT = isd.makeBoundVariableTerm(nl,varE)

      // forall x : Seq[Int], e : Int :: !isEmpty(x) -> tail(prepend(e,x)) == x
      val ts1 = isd.makeDTermSequence(nl,List(xT))
      val e1 = isd.makeDUnaryExpression(nl,Not(),isd.makeDDomainPredicateExpression(nl,isEmpty,ts1))
      val e2 = isd.makeDDomainFunctionApplicationTerm(nl,prepend,isd.makeDTermSequence(nl,List(eT,xT)))
      val e3 = isd.makeDEqualityExpression(nl,isd.makeDDomainFunctionApplicationTerm(nl,tail,isd.makeDTermSequence(nl,List(e2))),xT)
      val e4 = isd.makeDBinaryExpression(nl,ImplicationOperator(),e1,e3)
      val e = isd.makeDQuantifierExpression(nl,Forall, varX,isd.makeDQuantifierExpression(nl,Forall,varE,e4))
      isd.addDomainAxiom(nl,"equalitySymmetry", e)
    }

//    println(id.domain)
//    println(isd.domain)

    pf.defineReferenceField(nl,"Node.next")
    pf.defineDomainField(nl,"Node.val",integerType)
    pf.defineDomainField(nl,"Node.seq",integerSeqType)
  }

  def f(e : Expression)
  {
    e match {
      case PermissionExpression(_,_,_) => 0
      case UnfoldingExpression(_,_,_) => 1
      case EqualityExpression(_,_,_) => 2
      case UnaryExpression(_,_,_) => 3
      case BinaryExpression(_,_,_,_) => 4
      case DomainPredicateExpression(_,_,_) => 5
      case PredicateExpression(_,_,_) => 6
      case QuantifierExpression(_,_,_,_) => 7
    }
  }
  def f2(e : Expression)
  {
    e match {
      case PermissionExpression(_,_,_) => 0
      case UnfoldingExpression(_,_,_) => 1
      case EqualityExpression(_,_,_) => 2
      case UnaryExpression(_,_,_) => 3
      case BinaryExpression(_,_,_,_) => 4
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
  def g2(e : PExpression)
  {
    e match {
      case PEqualityExpression(_,_,_) => 2
      case PUnaryExpression(_,_,_) => 3
      case PBinaryExpression(_,_,_,_) => 4
      case PDomainPredicateExpression(_,_,_) => 5
      case PPredicateExpression(_,_,_) => 6
    }
  }

  def g2(e : PExpression)
  {
    e match {
      case PEqualityExpression(_,_,_) => 2
      case PUnaryExpression(_,_,_) => 3
      case PBinaryExpression(_,_,_,_) => 4
      case PDomainPredicateExpression(_,_,_) => 5
//      case PPredicateExpression(_,_,_) => 6
    }
  }

  def g(e : DExpression)
  {
    e match {
      case DEqualityExpression(_,_) => 2
      case DUnaryExpression(_,_) => 3
      case DBinaryExpression(_,_,_) => 4
      case DDomainPredicateExpression(_,_) => 5
//      case DQuantifierExpression(_,_,_) => 5
    }
  }
 */
}