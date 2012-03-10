package main

import silAST.programs.ProgramFactory
import silAST.symbols.logical.quantification.Forall
import silAST.symbols.logical.{And, Implication, Not}
import silAST.programs.symbols.PredicateFactory
import silAST.methods.MethodFactory
import silAST.source.noLocation
import silAST.types._
import silAST.expressions.util.{PTermSequence, TermSequence, DTermSequence}
import silAST.expressions.terms._
import silAST.expressions._

object Main {

  def main(args: Array[String]) {
    println("Hiho")
    makeProgram()
  }

  def makeProgram() {
    val nl = noLocation

    val pf = new ProgramFactory(nl, "P1")

    val sd = pf.getDomainFactory("Seq",List((nl,"T")))(nl);

    val tVarT = sd.makeVariableType(nl,sd.typeParameters(0))
    val tail = sd.defineDomainFunction(nl, "tail", DataTypeSequence(sd.thisType),sd.thisType)
    val prepend = sd.defineDomainFunction(nl, "prepend", DataTypeSequence(tVarT, sd.thisType), sd.thisType )
    val isEmpty = sd.defineDomainPredicate(nl, "isEmpty", DataTypeSequence(sd.thisType))

    val singleton = sd.defineDomainFunction(nl, "singleton", DataTypeSequence(tVarT), sd.thisType)

    {
      val varX = sd.makeBoundVariable(nl, "x", sd.thisType)
      val varE = sd.makeBoundVariable(nl, "y", tVarT)
      val xT = sd.makeBoundVariableTerm(nl, varX)
      val eT = sd.makeBoundVariableTerm(nl, varE)

      // forall x : Seq[T], e : T :: !isEmpty(x) -> tail(prepend(e,x)) == x
      val e1 = sd.makeDUnaryExpression(nl, Not()(nl), sd.makeDDomainPredicateExpression(nl, isEmpty, DTermSequence(xT)))
      val e2 = sd.makeDDomainFunctionApplicationTerm(nl, prepend, DTermSequence(eT,xT))
      val e3 = sd.makeDEqualityExpression(nl, sd.makeDDomainFunctionApplicationTerm(nl, tail, DTermSequence(e2)), xT)
      val e4 = sd.makeDBinaryExpression(nl, Implication()(nl), e1, e3)
      val e = sd.makeDQuantifierExpression(nl, Forall()(nl), varX, sd.makeDQuantifierExpression(nl, Forall()(nl), varE, e4))
      sd.addDomainAxiom(nl, "tailPrepend1", e)
    }

    val isd = pf.makeDomainInstance(sd,DataTypeSequence(integerType))
    val integerSeqType = isd.getType
    val singletonInt = isd.functions.find(_.name=="singleton").get
    val prependInt = isd.functions.find(_.name=="prepend").get

    val nextField = pf.defineField(nl, "Node.next",referenceType)
    val valField = pf.defineField(nl, "Node.val", integerType)
    val seqField = pf.defineField(nl, "Node.seq", integerSeqType)

    val vp: PredicateFactory = pf.getPredicateFactory(nl, "Node.valid");

    {
      //acc(val,100)
      // && acc(seq,50)
      // && acc(next,100)
      // && next!=null ==> next.valid && acc(next.seq,50) && seq==val :: next.seq
      // && next==null ==> seq==[val]
      val thisT = vp.makeProgramVariableTerm(nl, vp.thisVar)
      val this_val = vp.makeFieldReadTerm(nl, thisT, valField)
      val this_next = vp.makeFieldReadTerm(nl, thisT, nextField)
      val this_seq = vp.makeFieldReadTerm(nl, thisT, seqField)
      val this_next_seq = vp.makeFieldReadTerm(nl, this_next, seqField)

      val nullTerm = vp.makeDomainFunctionApplicationTerm(nl, nullFunction, TermSequence())
      val this_next_valid = vp.makePredicateExpression(nl, this_next, vp)
      val this_next_eq_null = vp.makeDomainFunctionApplicationTerm(nl,referenceEquality,TermSequence(this_next,nullTerm))
      val this_next_neq_null = vp.makeDomainFunctionApplicationTerm(nl, booleanNegation,TermSequence(this_next_eq_null))
//      val ite = vp.makeIfThenElseTerm(nl,this_next_neq_null,thisT,this_next)
      val singleton_this_val = vp.makeDomainFunctionApplicationTerm(nl, singletonInt, TermSequence(this_val))
      val acc_val_100 = vp.makePermissionExpression(nl, thisT,valField, vp.makeFullPermission(nl))
      val acc_next_100 = vp.makePermissionExpression(nl, thisT,nextField, vp.makeFullPermission(nl))
      val acc_seq_50 = vp.makePermissionExpression(nl, thisT,seqField, vp.makePercentagePermission(nl, vp.makeIntegerLiteralTerm(nl,50)))
      val acc_next_seq_50 = vp.makePermissionExpression(nl, this_next,seqField, vp.makePercentagePermission(nl, vp.makeIntegerLiteralTerm(nl,50)))
      val next_eq_null = vp.makeEqualityExpression(nl, this_next, nullTerm)
      val next_ne_null = vp.makeUnaryExpression(nl, Not()(nl), next_eq_null)
      val prepend_val_next_seq = vp.makeDomainFunctionApplicationTerm(nl, prependInt, TermSequence(this_val, this_next_seq))
      val seq_eq_prep = vp.makeEqualityExpression(nl, this_seq, prepend_val_next_seq)
      val seq_eq_singleton = vp.makeEqualityExpression(nl, this_seq, singleton_this_val)
      //next==null ==> seq==[val]
      val e1 = vp.makeBinaryExpression(nl, Implication()(nl), next_eq_null, seq_eq_singleton)
      //acc(next.seq,50) && seq==val :: next.seq
      val e2a = vp.makeBinaryExpression(nl, And()(nl), acc_next_seq_50, seq_eq_prep)
      val e2b = vp.makeBinaryExpression(nl, And()(nl), this_next_valid, e2a)
      // && next!=null ==> acc(next.seq,50) && seq==val :: next.seq
      val e2 = vp.makeBinaryExpression(nl, Implication()(nl), next_ne_null, e2b)
      val e3 = vp.makeBinaryExpression(nl, And()(nl), e1, e2)
      val e4 = vp.makeBinaryExpression(nl, And()(nl), acc_seq_50, acc_next_100)
      val e5 = vp.makeBinaryExpression(nl, And()(nl), e3, e4)
      val e = vp.makeBinaryExpression(nl, And()(nl), acc_val_100, e5)
      vp.setExpression(e)
      1
    }

    val ff = pf.getFunctionFactory(nl, "numXs", ((nl, "x", integerType)) :: Nil, integerType)

    {
      val x = ff.makeProgramVariableTerm(nl, ff.parameters(0))
      val v0 = ff.makeIntegerLiteralTerm(nl, 0)
      val v0_le_x = ff.makePDomainPredicateExpression(nl, integerLE, PTermSequence(v0,x))
      ff.addPrecondition(v0_le_x)

      val thisVar = ff.makeProgramVariableTerm(nl, ff.thisVar)
      val resultVar = ff.makeProgramVariableTerm(nl, ff.resultVar)
      val thisVar_next = ff.makePFieldReadTerm(nl, thisVar, nextField)

      //nonsensical - check recursion - next.numXs(x)
      val numXs_this_next = ff.makePFunctionApplicationTerm(nl, thisVar_next, ff, PTermSequence(x))
      val numXs_this_next_le_numXs_this = ff.makeDomainPredicateExpression(nl, integerLE, PTermSequence(numXs_this_next,resultVar))
      ff.addPostcondition(numXs_this_next_le_numXs_this)

      val numXs_this_next_plus_x = ff.makePDomainFunctionApplicationTerm(nl,integerAddition,PTermSequence(numXs_this_next,x))
      val b = ff.makePUnfoldingTerm(nl,thisVar,vp,numXs_this_next_plus_x)

      ff.setBody(b)

      val this_next_seq = ff.makePFieldReadTerm(nl, thisVar_next, seqField)
      ff.setMeasure(this_next_seq)
    }

    //insert(x:int)
    val mf: MethodFactory = pf.getMethodFactory(nl, "insert");

    {
      val xVar = mf.addParameter(nl, "x", integerType)
      val r = mf.addResult(nl, "r", integerType) //dummy for checking

      val this_var = mf.makeProgramVariableTerm(nl, mf.thisVar)
      val xTerm = mf.makeProgramVariableTerm(nl,xVar)
      val rTerm = mf.makeProgramVariableTerm(nl,r)
      val zeroTerm = mf.makeIntegerLiteralTerm(nl,0)


      val this_valid = mf.makePredicateExpression(nl, this_var, vp)
      mf.addPrecondition(nl, this_valid)
      mf.addPrecondition(nl, mf.makeDomainPredicateExpression(nl,integerLE,TermSequence(zeroTerm,xTerm)))
      mf.addPostcondition(nl, this_valid)
      mf.addPostcondition(nl, mf.makeDomainPredicateExpression(nl,integerLE,TermSequence(rTerm,xTerm)))

      val impl = mf.addImplementation(nl);

      {
        val nVar = impl.addLocalVariable(nl, "n", integerType)
        val xxVar = impl.addLocalVariable(nl, "xx", integerSeqType)

        val startBlock = impl.addFirstBasicBlock(nl, "start");
        val endBlock = impl.addLastBasicBlock(nl, "end");

        startBlock.addSuccessor(nl, startBlock, TrueExpression()(nl), true)
        startBlock.addSuccessor(nl, endBlock, TrueExpression()(nl), false)
        startBlock.addProgramVariableToScope(nVar)
        startBlock.addProgramVariableToScope(xxVar)

        {
          val this_term = startBlock.makeProgramVariableTerm(nl, mf.thisVar)
          val this_valid = startBlock.makePredicateExpression(nl, this_term, vp)
          startBlock.appendInhale(nl, this_valid)
          startBlock.appendUnfold(nl, this_valid)

          val nTerm = startBlock.makeProgramVariableTerm(nl, nVar)
          //this.numXs(n)
          val numXs_nTerm = startBlock.makePFunctionApplicationTerm(nl, this_term, ff, PTermSequence(nTerm))
          startBlock.appendAssignment(nl, nVar, numXs_nTerm)


          startBlock.appendFold(nl, this_valid)
        }


        1
      }

      val bdf = pf.getDomainFactory("BB",List((nl,"T")))(nl);
      val bd = bdf.compile

      {
        val bdI = pf.makeDomainInstance(bdf,DataTypeSequence(integerType))
        val bdI2 = pf.makeDomainInstance(bdf,DataTypeSequence(integerType))
        
        val bdIt = bdI.getType
        
        val bdItd = bdIt.domain

        assert (bdI eq bdI2)
        assert (bdI eq bdItd)

        1
      }
     1
    }

    val p = pf.getProgram

    println(p.toString)
    
    println(integerAddition.domain.name)

  }

  def f(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PermissionExpression(_, _, _) => 0
      case UnfoldingExpression( _, _) => 1
      case EqualityExpression( _, _) => 2
      case UnaryExpression( _, _) => 3
      case BinaryExpression( _, _, _) => 4
      case DomainPredicateExpression( _, _) => 5
      case PredicateExpression( _, _) => 6
      case QuantifierExpression( _, _, _) => 7
    }
  }

  def f2(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PermissionExpression(_, _, _) => 0
      case UnfoldingExpression( _, _) => 1
      case EqualityExpression( _, _) => 2
      case UnaryExpression( _, _) => 3
      case BinaryExpression( _, _, _) => 4
      case DomainPredicateExpression( _, _) => 5
      case PredicateExpression( _, _) => 6
      //      case QuantifierExpression(_,_,_) => 7
    }
  }

  def g(t: Term) {
    t match {
      case OldTerm(_) => 1
      case LiteralTerm() => 1

      case LogicalVariableTerm( _) => 1
      case FunctionApplicationTerm( _, _, _) => 3
      case DomainFunctionApplicationTerm(_, _) => 3

      case ProgramVariableTerm(_) => 2
      case CastTerm(_, _) => 2
      case FieldReadTerm(_, _) => 6

      case UnfoldingTerm(_, _,_) => 6
    }

    t match {
      case LiteralTerm() => 1

      case LogicalVariableTerm( _) => 1
      case FunctionApplicationTerm(_, _, _) => 3
      //      case DomainFunctionApplicationTerm(_,_,_) => 3

      case ProgramVariableTerm(_) => 2
      case CastTerm(_, _) => 2
      case FieldReadTerm(_, _) => 6
    }
  }
}