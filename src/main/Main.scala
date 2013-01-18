package main

import semper.sil.ast.programs.ProgramFactory
import semper.sil.ast.symbols.logical.quantification.Forall
import semper.sil.ast.symbols.logical.{And, Implication, Not}
import semper.sil.ast.programs.symbols.PredicateFactory
import semper.sil.ast.methods.MethodFactory
import semper.sil.ast.source.NoLocation
import semper.sil.ast.types._
import semper.sil.ast.expressions.util.ExpressionSequence
import semper.sil.ast.expressions.terms._
import semper.sil.ast.expressions._

object Main {

  def main(args: Array[String]) {
    println("Hiho")
    makeProgram()
  }

  def makeProgram() {
    val nl = NoLocation

    val pf = new ProgramFactory("P1")(nl,"Program1" :: Nil)

    val sd = pf.getDomainFactory("Seq", List((nl, "T",List("Element type"))),nl)

    val tVarT = sd.makeVariableType(sd.typeParameters(0),nl)
    val tail = sd.defineDomainFunction("tail", DataTypeSequence(sd.thisType), sd.thisType,nl)
    val prepend = sd.defineDomainFunction("prepend", DataTypeSequence(tVarT, sd.thisType), sd.thisType,nl)
    val isEmpty = sd.defineDomainPredicate("isEmpty", DataTypeSequence(sd.thisType),nl)

    val singleton = sd.defineDomainFunction("singleton", DataTypeSequence(tVarT), sd.thisType,nl)

    {
      val varX = sd.makeBoundVariable("x", sd.thisType,nl)
      val varE = sd.makeBoundVariable("y", tVarT,nl)
      val xT = sd.makeBoundVariableExpression(varX,nl)
      val eT = sd.makeBoundVariableExpression(varE,nl)

      // forall x : Seq[T], e : T :: !isEmpty(x) -> tail(prepend(e,x)) == x
      val e1 = sd.makeUnaryExpression(Not()(nl), sd.makeDomainPredicateExpression(isEmpty, ExpressionSequence(xT),nl),nl)
      val e2 = sd.makeDomainFunctionApplicationExpression(prepend, ExpressionSequence(eT, xT),nl)
      val e3 = sd.makeEqualityExpression(sd.makeDomainFunctionApplicationExpression(tail, ExpressionSequence(e2),nl), xT,nl)
      val e4 = sd.makeBinaryExpression(Implication()(nl), e1, e3,nl)
      val e = sd.makeQuantifierExpression(Forall()(nl), varX, sd.makeQuantifierExpression(Forall()(nl), varE, e4)(nl))(nl)
      sd.addDomainAxiom("tailPrepend1", e,nl)
    }

    val isd = pf.makeDomainInstance(sd, DataTypeSequence(integerType))
    val integerSeqType = isd.getType
    val singletonInt = isd.functions.find(_.name == "singleton").get
    val prependInt = isd.functions.find(_.name == "prepend").get

    val nextField = pf.defineField("Node.next", referenceType)(nl)
    val valField = pf.defineField("Node.val", integerType)(nl)
    val seqField = pf.defineField("Node.seq", integerSeqType)(nl)

    val vp: PredicateFactory = pf.getPredicateFactory("Node.valid",nl)

    {
      //acc(val,100)
      // && acc(seq,50)
      // && acc(next,100)
      // && next!=null ==> next.valid && acc(next.seq,50) && seq==val :: next.seq
      // && next==null ==> seq==[val]
      val thisT = vp.makeProgramVariableExpression(vp.thisVar,nl)
      val this_val = vp.makeFieldReadExpression(thisT, valField,nl)
      val this_next = vp.makeFieldReadExpression(thisT, nextField,nl)
      val this_seq = vp.makeFieldReadExpression(thisT, seqField,nl)
      val this_next_seq = vp.makeFieldReadExpression(this_next, seqField,nl)

      val nullExpression = vp.makeDomainFunctionApplicationExpression(nullFunction, ExpressionSequence(),nl)
      val this_next_valid = vp.makePredicatePermissionExpression(this_next, vp,vp.makeFullPermission(nl), nl)
      val this_next_eq_null = vp.makeDomainFunctionApplicationExpression(referenceEquality, ExpressionSequence(this_next, nullExpression),nl)
      val this_next_neq_null = vp.makeDomainFunctionApplicationExpression(booleanNegation, ExpressionSequence(this_next_eq_null),nl)
      //      val ite = vp.makeIfThenElseExpression(nl,this_next_neq_null,thisT,this_next)
      val singleton_this_val = vp.makeDomainFunctionApplicationExpression(singletonInt, ExpressionSequence(this_val),nl)
      val acc_val_100 = vp.makeFieldPermissionExpression(thisT, valField, vp.makeFullPermission(nl),nl)
      val acc_next_100 = vp.makeFieldPermissionExpression(thisT, nextField, vp.makeFullPermission(nl),nl)
      val acc_seq_50 = vp.makeFieldPermissionExpression(thisT, seqField, vp.makePercentagePermission(vp.makeIntegerLiteralExpression(50,nl),nl),nl)
      val acc_next_seq_50 = vp.makeFieldPermissionExpression(this_next, seqField, vp.makePercentagePermission(vp.makeIntegerLiteralExpression(50,nl),nl),nl)
      val next_eq_null = vp.makeEqualityExpression(this_next, nullExpression,nl)
      val next_ne_null = vp.makeUnaryExpression(Not()(nl), next_eq_null,nl)
      val prepend_val_next_seq = vp.makeDomainFunctionApplicationExpression(prependInt, ExpressionSequence(this_val, this_next_seq),nl)
      val seq_eq_prep = vp.makeEqualityExpression(this_seq, prepend_val_next_seq,nl)
      val seq_eq_singleton = vp.makeEqualityExpression(this_seq, singleton_this_val,nl)
      //next==null ==> seq==[val]
      val e1 = vp.makeBinaryExpression(Implication()(nl), next_eq_null, seq_eq_singleton,nl)
      //acc(next.seq,50) && seq==val :: next.seq
      val e2a = vp.makeBinaryExpression(And()(nl), acc_next_seq_50, seq_eq_prep,nl)
      val e2b = vp.makeBinaryExpression(And()(nl), this_next_valid, e2a,nl)
      // && next!=null ==> acc(next.seq,50) && seq==val :: next.seq
      val e2 = vp.makeBinaryExpression(Implication()(nl), next_ne_null, e2b,nl)
      val e3 = vp.makeBinaryExpression(And()(nl), e1, e2,nl)
      val e4 = vp.makeBinaryExpression(And()(nl), acc_seq_50, acc_next_100,nl)
      val e5 = vp.makeBinaryExpression(And()(nl), e3, e4,nl)
      val e = vp.makeBinaryExpression(And()(nl), acc_val_100, e5,nl)
      vp.setExpression(e)
      1
    }

    val ff = pf.getFunctionFactory("numXs", ((nl, "x", integerType)) :: Nil, integerType,nl,List("number of Xs"))

    {
      val x = ff.makeProgramVariableExpression(ff.parameters(0),nl)
      val v0 = ff.makeIntegerLiteralExpression(0,nl)
      val v0_le_x = ff.makeDomainPredicateExpression(booleanEvaluate,ExpressionSequence(ff.makeDomainFunctionApplicationExpression(integerLE, ExpressionSequence(v0, x),nl)),nl)
      ff.addPrecondition(v0_le_x)

      val thisVar = ff.makeProgramVariableExpression(ff.thisVar,nl)
      val resultVar = ff.makeProgramVariableExpression(ff.resultVar,nl)
      val thisVar_next = ff.makeFieldReadExpression(thisVar, nextField,nl)

      //nonsensical - check recursion - next.numXs(x)
      val numXs_this_next = ff.makeFunctionApplicationExpression(thisVar_next, ff, ExpressionSequence(x),nl)
      val numXs_this_next_le_numXs_this = ff.makeDomainPredicateExpression(booleanEvaluate,ExpressionSequence(ff.makeDomainFunctionApplicationExpression(integerLE, ExpressionSequence(numXs_this_next, resultVar),nl)),nl)
      ff.addPostcondition(numXs_this_next_le_numXs_this)

      val numXs_this_next_plus_x = ff.makeDomainFunctionApplicationExpression(integerAddition, ExpressionSequence(numXs_this_next, x),nl)
      val acc_thisVar_valid_write = ff.makePredicatePermissionExpression(thisVar, vp, ff.makeFullPermission(nl),nl)
      val b = ff.makeUnfoldingExpression(acc_thisVar_valid_write,numXs_this_next_plus_x,nl)

      ff.setBody(b)

      val this_next_seq = ff.makeFieldReadExpression(thisVar_next, seqField,nl)
      ff.setMeasure(this_next_seq)
    }

    //insert(x:int)
    val mf: MethodFactory = pf.getMethodFactory("insert")(nl)

    {
      val xVar = mf.addParameter("x", integerType,nl)
      val thisVar = mf.addParameter("this", referenceType,nl)
      val r = mf.addResult("r", integerType,nl) //dummy for checking

      val this_var = mf.makeProgramVariableExpression(thisVar,nl)
      val xExpression = mf.makeProgramVariableExpression(xVar,nl)
      val rExpression = mf.makeProgramVariableExpression(r,nl)
      val zeroExpression = mf.makeIntegerLiteralExpression(0,nl)

      val this_valid = mf.makePredicatePermissionExpression(this_var, vp,vp.makeFullPermission(nl), nl)
      mf.addPrecondition(this_valid,nl)
      mf.addPrecondition(mf.makeDomainPredicateExpression(booleanEvaluate,ExpressionSequence(mf.makeDomainFunctionApplicationExpression(integerLE, ExpressionSequence(zeroExpression, xExpression),nl)),nl),nl)
      mf.addPostcondition(this_valid,nl)
      mf.addPostcondition(mf.makeDomainPredicateExpression(booleanEvaluate,ExpressionSequence(mf.makeDomainFunctionApplicationExpression(integerLE, ExpressionSequence(rExpression, xExpression),nl)),nl),nl)

      val impl = mf.addImplementation(nl)

      {
        val nVar = impl.addProgramVariable("n", integerType)(nl)
        val xxVar = impl.addProgramVariable("xx", integerSeqType)(nl)
        val rVar = impl.addProgramVariable("pointer", referenceType)(nl)


        val startBlock = impl.cfgFactory.addBasicBlock("start",nl)
        val midBlock = impl.cfgFactory.addLoopBlock("mid", TrueExpression()(nl),nl)
        val endBlock = impl.cfgFactory.addBasicBlock("end",nl)
        endBlock.setHalt(nl,"enough!" :: Nil)
        impl.cfgFactory.setStartNode(startBlock)
        impl.cfgFactory.setEndNode(endBlock)

        startBlock.setBranch(TrueExpression()(nl), midBlock, endBlock,nl)
        midBlock.setGoto(endBlock,nl)
        midBlock.setInvariant(TrueExpression()(nl))

        {
          val this_term = startBlock.makeProgramVariableExpression(thisVar,nl)
          val rVar_term = startBlock.makeProgramVariableExpression(rVar,nl)
          val this_valid = startBlock.makePredicatePermissionExpression(this_term, vp,vp.makeFullPermission(nl), nl)
          startBlock.appendInhale(this_valid,nl)
          startBlock.appendUnfold(startBlock.makePredicatePermissionExpression(this_term,vp,vp.makeFullPermission(nl),nl),nl)

          val nExpression = startBlock.makeProgramVariableExpression(nVar,nl)
          //this.numXs(n)
          val numXs_nExpression = startBlock.makeFunctionApplicationExpression(this_term, ff, ExpressionSequence(nExpression),nl)
          startBlock.appendAssignment(nVar, numXs_nExpression,nl)
          //This means exhale of predicate expression
          startBlock.appendExhale(vp.predicate.expression.substitute(impl.makeProgramVariableSubstitution(Set((vp.thisVar,rVar_term)))),Some("bugger"),nl)
          val pe = startBlock.makePredicatePermissionExpression(rVar_term,vp,vp.makeFullPermission(nl),nl)
          startBlock.appendAssignment(rVar,startBlock.makeUnfoldingExpression(pe,rExpression,nl),nl)

          startBlock.appendFold(this_term, vp,vp.makeFullPermission(nl),nl)
          val lb = midBlock.bodyFactory.addBasicBlock("whileBody",nl)
          lb.appendAssignment(nVar, numXs_nExpression,nl)
          lb.setHalt(nl)
          midBlock.bodyFactory.setStartNode(lb)
          midBlock.bodyFactory.setEndNode(lb)
        }


        1
      }

      val bdf = pf.getDomainFactory("BB", List((nl, "T",List("Element type","covariant"))),nl)
      bdf.defineDomainFunction("ff",DataTypeSequence(integerType),integerType,nl)
      val bd = bdf.compile()

      {
        val bdI = pf.makeDomainInstance(bdf, DataTypeSequence(integerType))
        val bdI2 = pf.makeDomainInstance(bdf, DataTypeSequence(integerType))

        val bdIt = bdI.getType

        val bdItd = bdIt.domain

        assert(bdI eq bdI2)
        assert(bdI eq bdItd)

        1
      }
      
      // Domain with no type parameters
      val sdf = pf.getDomainFactory("SD",Nil,nl)
      sdf.defineDomainFunction("sf",DataTypeSequence(),integerType,nl)
      sdf.defineDomainPredicate("sp",DataTypeSequence(),nl)
      val sd = sdf.compile()
      val sdI = pf.makeDomainInstance(sdf, DataTypeSequence())
    }

    val p = pf.getProgram

    println(p.toString)

  }

  def f(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PredicatePermissionExpression(_, _) => 0
      case FieldPermissionExpression(_, _) => 0
      case UnfoldingExpression( _,_) => 1
      case EqualityExpression(_, _) => 2
      case UnaryExpression(_, _) => 3
      case BinaryExpression(_, _, _) => 4
      case DomainPredicateExpression(_, _) => 5
//      case QuantifierExpression(_, _, _) => 7
    }
  }

  def fef(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PredicatePermissionExpression(_, _) => 0
      case FieldPermissionExpression(_, _) => 0
      case UnfoldingExpression( _,_) => 1
      case EqualityExpression(_, _) => 2
      case UnaryExpression(_, _) => 3
      case BinaryExpression(_, _, _) => 4
      case DomainPredicateExpression(_, _) => 5
      case QuantifierExpression(_, _, _) => 7
    }
  }

  def f2(e: Expression) {
    e match {
      case OldExpression(_) => 0
      case TrueExpression() => 0
      case FalseExpression() => 0
      case PredicatePermissionExpression(_, _) => 0
      case FieldPermissionExpression(_, _) => 0
      case UnfoldingExpression(_, _) => 1
      case EqualityExpression(_, _) => 2
      case UnaryExpression(_, _) => 3
      case BinaryExpression(_, _, _) => 4
      case DomainPredicateExpression(_, _) => 5
      case QuantifierExpression(_,_,_) => 7
    }
  }

  def g(t: Expression) {
    t match {
      case OldExpression(_) => 1
      case IntegerLiteralExpression(_) => 1
      case IfThenElseExpression(_, _,_) => 7

      case LogicalVariableExpression(_) => 1
      case FunctionApplicationExpression(_, _, _) => 3
      case DomainFunctionApplicationExpression(_, _) => 3

      case ProgramVariableExpression(_) => 2
      case CastExpression(_, _) => 2
      case FieldReadExpression(_) => 6

      case UnfoldingExpression(_, _) => 6
      case PermExpression(_) => 19
    }

    t match {
      case IntegerLiteralExpression(_) => 1

      case LogicalVariableExpression(_) => 1
      case FunctionApplicationExpression(_, _, _) => 3
      //      case DomainFunctionApplicationExpression(_,_,_) => 3

      case ProgramVariableExpression(_) => 2
      case CastExpression(_, _) => 2
      case FieldReadExpression(_) => 6
    }
  }

}