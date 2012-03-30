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

    val pf = new ProgramFactory("P1")(nl)

    val sd = pf.getDomainFactory("Seq", List((nl, "T")))(nl);

    val tVarT = sd.makeVariableType(sd.typeParameters(0))(nl)
    val tail = sd.defineDomainFunction("tail", DataTypeSequence(sd.thisType), sd.thisType)(nl)
    val prepend = sd.defineDomainFunction("prepend", DataTypeSequence(tVarT, sd.thisType), sd.thisType)(nl)
    val isEmpty = sd.defineDomainPredicate("isEmpty", DataTypeSequence(sd.thisType))(nl)

    val singleton = sd.defineDomainFunction("singleton", DataTypeSequence(tVarT), sd.thisType)(nl)

    {
      val varX = sd.makeBoundVariable("x", sd.thisType)(nl)
      val varE = sd.makeBoundVariable("y", tVarT)(nl)
      val xT = sd.makeBoundVariableTerm(varX)(nl)
      val eT = sd.makeBoundVariableTerm(varE)(nl)

      // forall x : Seq[T], e : T :: !isEmpty(x) -> tail(prepend(e,x)) == x
      val e1 = sd.makeDUnaryExpression(Not()(nl), sd.makeDDomainPredicateExpression(isEmpty, DTermSequence(xT))(nl))(nl)
      val e2 = sd.makeDDomainFunctionApplicationTerm(prepend, DTermSequence(eT, xT))(nl)
      val e3 = sd.makeDEqualityExpression(sd.makeDDomainFunctionApplicationTerm(tail, DTermSequence(e2))(nl), xT)(nl)
      val e4 = sd.makeDBinaryExpression(Implication()(nl), e1, e3)(nl)
      val e = sd.makeDQuantifierExpression(Forall()(nl), varX, sd.makeDQuantifierExpression(Forall()(nl), varE, e4)(nl))(nl)
      sd.addDomainAxiom("tailPrepend1", e)(nl)
    }

    val isd = pf.makeDomainInstance(sd, DataTypeSequence(integerType))
    val integerSeqType = isd.getType
    val singletonInt = isd.functions.find(_.name == "singleton").get
    val prependInt = isd.functions.find(_.name == "prepend").get

    val nextField = pf.defineField("Node.next", referenceType)(nl)
    val valField = pf.defineField("Node.val", integerType)(nl)
    val seqField = pf.defineField("Node.seq", integerSeqType)(nl)

    val vp: PredicateFactory = pf.getPredicateFactory("Node.valid")(nl);

    {
      //acc(val,100)
      // && acc(seq,50)
      // && acc(next,100)
      // && next!=null ==> next.valid && acc(next.seq,50) && seq==val :: next.seq
      // && next==null ==> seq==[val]
      val thisT = vp.makeProgramVariableTerm(vp.thisVar)(nl)
      val this_val = vp.makeFieldReadTerm(thisT, valField)(nl)
      val this_next = vp.makeFieldReadTerm(thisT, nextField)(nl)
      val this_seq = vp.makeFieldReadTerm(thisT, seqField)(nl)
      val this_next_seq = vp.makeFieldReadTerm(this_next, seqField)(nl)

      val nullTerm = vp.makeDomainFunctionApplicationTerm(nullFunction, TermSequence())(nl)
      val this_next_valid = vp.makePredicateExpression(this_next, vp)(nl)
      val this_next_eq_null = vp.makeDomainFunctionApplicationTerm(referenceEquality, TermSequence(this_next, nullTerm))(nl)
      val this_next_neq_null = vp.makeDomainFunctionApplicationTerm(booleanNegation, TermSequence(this_next_eq_null))(nl)
      //      val ite = vp.makeIfThenElseTerm(nl,this_next_neq_null,thisT,this_next)
      val singleton_this_val = vp.makeDomainFunctionApplicationTerm(singletonInt, TermSequence(this_val))(nl)
      val acc_val_100 = vp.makePermissionExpression(thisT, valField, vp.makeFullPermission()(nl))(nl)
      val acc_next_100 = vp.makePermissionExpression(thisT, nextField, vp.makeFullPermission()(nl))(nl)
      val acc_seq_50 = vp.makePermissionExpression(thisT, seqField, vp.makePercentagePermission(vp.makeIntegerLiteralTerm(50)(nl))(nl))(nl)
      val acc_next_seq_50 = vp.makePermissionExpression(this_next, seqField, vp.makePercentagePermission(vp.makeIntegerLiteralTerm(50)(nl))(nl))(nl)
      val next_eq_null = vp.makeEqualityExpression(this_next, nullTerm)(nl)
      val next_ne_null = vp.makeUnaryExpression(Not()(nl), next_eq_null)(nl)
      val prepend_val_next_seq = vp.makeDomainFunctionApplicationTerm(prependInt, TermSequence(this_val, this_next_seq))(nl)
      val seq_eq_prep = vp.makeEqualityExpression(this_seq, prepend_val_next_seq)(nl)
      val seq_eq_singleton = vp.makeEqualityExpression(this_seq, singleton_this_val)(nl)
      //next==null ==> seq==[val]
      val e1 = vp.makeBinaryExpression(Implication()(nl), next_eq_null, seq_eq_singleton)(nl)
      //acc(next.seq,50) && seq==val :: next.seq
      val e2a = vp.makeBinaryExpression(And()(nl), acc_next_seq_50, seq_eq_prep)(nl)
      val e2b = vp.makeBinaryExpression(And()(nl), this_next_valid, e2a)(nl)
      // && next!=null ==> acc(next.seq,50) && seq==val :: next.seq
      val e2 = vp.makeBinaryExpression(Implication()(nl), next_ne_null, e2b)(nl)
      val e3 = vp.makeBinaryExpression(And()(nl), e1, e2)(nl)
      val e4 = vp.makeBinaryExpression(And()(nl), acc_seq_50, acc_next_100)(nl)
      val e5 = vp.makeBinaryExpression(And()(nl), e3, e4)(nl)
      val e = vp.makeBinaryExpression(And()(nl), acc_val_100, e5)(nl)
      vp.setExpression(e)
      1
    }

    val ff = pf.getFunctionFactory("numXs", ((nl, "x", integerType)) :: Nil, integerType)(nl)

    {
      val x = ff.makeProgramVariableTerm(ff.parameters(0))(nl)
      val v0 = ff.makeIntegerLiteralTerm(0)(nl)
      val v0_le_x = ff.makePDomainPredicateExpression(integerLE, PTermSequence(v0, x))(nl)
      ff.addPrecondition(v0_le_x)

      val thisVar = ff.makeProgramVariableTerm(ff.thisVar)(nl)
      val resultVar = ff.makeProgramVariableTerm(ff.resultVar)(nl)
      val thisVar_next = ff.makePFieldReadTerm(thisVar, nextField)(nl)

      //nonsensical - check recursion - next.numXs(x)
      val numXs_this_next = ff.makePFunctionApplicationTerm(thisVar_next, ff, PTermSequence(x))(nl)
      val numXs_this_next_le_numXs_this = ff.makeDomainPredicateExpression(integerLE, PTermSequence(numXs_this_next, resultVar))(nl)
      ff.addPostcondition(numXs_this_next_le_numXs_this)

      val numXs_this_next_plus_x = ff.makePDomainFunctionApplicationTerm(integerAddition, PTermSequence(numXs_this_next, x))(nl)
      val b = ff.makePUnfoldingTerm(thisVar, vp, numXs_this_next_plus_x)(nl)

      ff.setBody(b)

      val this_next_seq = ff.makePFieldReadTerm(thisVar_next, seqField)(nl)
      ff.setMeasure(this_next_seq)
    }

    //insert(x:int)
    val mf: MethodFactory = pf.getMethodFactory("insert")(nl)

    {
      val xVar = mf.addParameter("x", integerType)(nl)
      val thisVar = mf.addParameter("this", referenceType)(nl)
      val r = mf.addResult("r", integerType)(nl) //dummy for checking

      val this_var = mf.makeProgramVariableTerm(thisVar)(nl)
      val xTerm = mf.makeProgramVariableTerm(xVar)(nl)
      val rTerm = mf.makeProgramVariableTerm(r)(nl)
      val zeroTerm = mf.makeIntegerLiteralTerm(0)(nl)


      val this_valid = mf.makePredicateExpression(this_var, vp)(nl)
      mf.addPrecondition(this_valid)(nl)
      mf.addPrecondition(mf.makeDomainPredicateExpression(integerLE, TermSequence(zeroTerm, xTerm))(nl))(nl)
      mf.addPostcondition(this_valid)(nl)
      mf.addPostcondition(mf.makeDomainPredicateExpression(integerLE, TermSequence(rTerm, xTerm))(nl))(nl)

      val impl = mf.addImplementation()(nl);

      {
        val nVar = impl.addProgramVariable("n", integerType)(nl)
        val xxVar = impl.addProgramVariable("xx", integerSeqType)(nl)


        val startBlock = impl.cfgFactory.addBasicBlock("start")(nl);
        val midBlock = impl.cfgFactory.addLoopBlock("mid", TrueExpression()(nl))(nl);
        val endBlock = impl.cfgFactory.addBasicBlock("end")(nl);
        endBlock.setHalt()(nl)
        impl.cfgFactory.setStartNode(startBlock)
        impl.cfgFactory.setEndNode(endBlock)

        startBlock.setBranch(TrueExpression()(nl), midBlock, endBlock)(nl)
        midBlock.setGoto(endBlock)(nl)
        midBlock.setInvariant(TrueExpression()(nl))

        {
          val this_term = startBlock.makeProgramVariableTerm(thisVar)(nl)
          val this_valid = startBlock.makePredicateExpression(this_term, vp)(nl)
          startBlock.appendInhale(this_valid)(nl)
          startBlock.appendUnfold(this_valid)(nl)

          val nTerm = startBlock.makeProgramVariableTerm(nVar)(nl)
          //this.numXs(n)
          val numXs_nTerm = startBlock.makePFunctionApplicationTerm(this_term, ff, PTermSequence(nTerm))(nl)
          startBlock.appendAssignment(nVar, numXs_nTerm)(nl)


          startBlock.appendFold(this_valid)(nl)
          val lb = midBlock.bodyFactory.addBasicBlock("whileBody")(nl)
          lb.appendAssignment(nVar, numXs_nTerm)(nl)
          lb.setHalt()(nl)
          midBlock.bodyFactory.setStartNode(lb)
          midBlock.bodyFactory.setEndNode(lb)
        }


        1
      }

      val bdf = pf.getDomainFactory("BB", List((nl, "T")))(nl);
      val bd = bdf.compile

      {
        val bdI = pf.makeDomainInstance(bdf, DataTypeSequence(integerType))
        val bdI2 = pf.makeDomainInstance(bdf, DataTypeSequence(integerType))

        val bdIt = bdI.getType

        val bdItd = bdIt.domain

        assert(bdI eq bdI2)
        assert(bdI eq bdItd)

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
      case UnfoldingExpression(_, _) => 1
      case EqualityExpression(_, _) => 2
      case UnaryExpression(_, _) => 3
      case BinaryExpression(_, _, _) => 4
      case DomainPredicateExpression(_, _) => 5
      case PredicateExpression(_, _) => 6
      case QuantifierExpression(_, _, _) => 7
    }
  }

  def f2(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PermissionExpression(_, _, _) => 0
      case UnfoldingExpression(_, _) => 1
      case EqualityExpression(_, _) => 2
      case UnaryExpression(_, _) => 3
      case BinaryExpression(_, _, _) => 4
      case DomainPredicateExpression(_, _) => 5
      case PredicateExpression(_, _) => 6
      //      case QuantifierExpression(_,_,_) => 7
    }
  }

  def g(t: Term) {
    t match {
      case OldTerm(_) => 1
      case LiteralTerm() => 1

      case LogicalVariableTerm(_) => 1
      case FunctionApplicationTerm(_, _, _) => 3
      case DomainFunctionApplicationTerm(_, _) => 3

      case ProgramVariableTerm(_) => 2
      case CastTerm(_, _) => 2
      case FieldReadTerm(_, _) => 6

      case UnfoldingTerm(_, _, _) => 6
    }

    t match {
      case LiteralTerm() => 1

      case LogicalVariableTerm(_) => 1
      case FunctionApplicationTerm(_, _, _) => 3
      //      case DomainFunctionApplicationTerm(_,_,_) => 3

      case ProgramVariableTerm(_) => 2
      case CastTerm(_, _) => 2
      case FieldReadTerm(_, _) => 6
    }
  }
}