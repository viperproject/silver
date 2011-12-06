package main

import silAST.expressions._
import terms._
import silAST.programs.ProgramFactory
import silAST.symbols.logical.quantification.Forall
import silAST.source.noLocation
import silAST.symbols.logical.{AndOperator, ImplicationOperator, Not}
import com.sun.istack.internal.Pool.Impl
import silAST.programs.symbols.PredicateFactory

object Main {

  def main(args: Array[String]) {
    println("Hiho")
    makeProgram()
  }

  def makeProgram() = {
    val nl = noLocation

    val pf = new ProgramFactory("P1")

    val id = pf.getDomainFactory("Integer")(nl);
    val integerType = pf.makeNonReferenceDataType(nl,id)
    val isd = pf.getDomainFactory("IntegerSeq")(nl);
    val integerSeqType = pf.makeNonReferenceDataType(nl,isd);

    val sigTail = isd.defineDomainFunctionSignature(nl,isd.makeDataTypeSequence(List(integerSeqType)),integerSeqType)
    val tail = isd.defineDomainFunction(nl,"tail",sigTail)
    val sigPrepend = isd.defineDomainFunctionSignature(nl,isd.makeDataTypeSequence(List(integerType,integerSeqType)),integerSeqType)
    val prepend = isd.defineDomainFunction(nl,"prepend",sigPrepend)
    val sigP = isd.defineDomainPredicateSignature(nl,isd.makeDataTypeSequence(List(integerSeqType)))
    val isEmpty = isd.defineDomainPredicate(nl,"isEmpty",sigP)

    val sigSingleton = isd.defineDomainFunctionSignature(nl,isd.makeDataTypeSequence(List(integerType)),integerSeqType)
    val singleton = isd.defineDomainFunction(nl,"singleton",sigSingleton)

    {
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
      isd.addDomainAxiom(nl,"tailPrepend1", e)
    }

//    println(id.domain)
//    println(isd.domain)

    val nextField = pf.defineReferenceField(nl,"Node.next")
    val valField = pf.defineDomainField(nl,"Node.val",integerType)
    val seqField = pf.defineDomainField(nl,"Node.seq",integerSeqType)

    val ppf : PredicateFactory = pf.getPredicateFactory(nl,"Node.valid");

    {
      //acc(val,100)
      // && acc(seq,50)
      // && acc(next,100)
      // && next!=null ==> acc(next.seq,50) && seq==val :: next.seq
      // && next==null ==> seq==[val]
      val thisT = ppf.makeProgramVariableTerm(nl, ppf.thisVar)
      val this_val = ppf.makeFieldReadTerm(nl,thisT,valField)
      val this_next = ppf.makeFieldReadTerm(nl,thisT,nextField)
      val this_seq = ppf.makeFieldReadTerm(nl,thisT,seqField)
      val this_next_seq = ppf.makeFieldReadTerm(nl,this_next,seqField)
      val this_val_as = ppf.makeTermSequence(nl,List(this_val))
      val singleton_this_val = ppf.makeDomainFunctionApplicationTerm(nl,singleton,this_val_as)
      val emptyParameters = ppf.makeTermSequence(nl, List.empty[Term])
      val nullTerm = ppf.makeDomainFunctionApplicationTerm(nl,ppf.nullFunction,emptyParameters)
      val acc_val_100 = ppf.makePermissionExpression(nl,this_val,ppf.makeFullPermissionTerm())
      val acc_next_100 = ppf.makePermissionExpression(nl,this_next,ppf.makeFullPermissionTerm())
      val acc_seq_50   = ppf.makePermissionExpression(nl,this_seq,ppf.makePercentagePermissionTerm (nl,50))
      val acc_next_seq_50 = ppf.makePermissionExpression(nl,this_next_seq,ppf.makePercentagePermissionTerm (nl,50))
      val next_eq_null = ppf.makeEqualityExpression(nl,this_next,nullTerm)
      val next_ne_null = ppf.makeUnaryExpression(nl,Not(),next_eq_null)
      val val_next_seq_as = ppf.makeTermSequence(nl,List(this_val,this_next_seq))
      val prepend_val_next_seq = ppf.makeDomainFunctionApplicationTerm(nl,prepend,val_next_seq_as)
      val seq_eq_prep = ppf.makeEqualityExpression(nl,this_seq,prepend_val_next_seq)
      val seq_eq_singleton = ppf.makeEqualityExpression(nl,this_seq,singleton_this_val)
      //next==null ==> seq==[val]
      val e1 = ppf.makeBinaryExpression(nl,ImplicationOperator(),next_eq_null,seq_eq_singleton)
      //acc(next.seq,50) && seq==val :: next.seq
      val e2a = ppf.makeBinaryExpression(nl,AndOperator(),acc_next_seq_50,seq_eq_prep)
      // && next!=null ==> acc(next.seq,50) && seq==val :: next.seq
      val e2 = ppf.makeBinaryExpression(nl,ImplicationOperator(),next_ne_null,e2a)
      val e3 = ppf.makeBinaryExpression(nl,AndOperator(),e1,e2)
      val e4 = ppf.makeBinaryExpression(nl,AndOperator(),acc_seq_50,acc_next_100)
      val e5 = ppf.makeBinaryExpression(nl,AndOperator(),e3,e4)
      val e = ppf.makeBinaryExpression(nl,AndOperator(),acc_val_100,e5)
      ppf.setExpression(e)
      1
    }

    val mf = pf.getMethodFactory(nl,"insert");

    {
      mf.
      1
    }

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