package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast._
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.plugin.standard.decreases.DecreasesTuple
import viper.silver.verifier.ConsistencyError

import scala.collection.immutable.ListMap

/**
  * A basic interface to help create termination checks.
  *
  * The following features have to be defined in the program (program field of ProgramManager)
  * otherwise a consistency error is issued.
  * "decreasing" domain function
  * "bounded" domain function
  */
trait DecreasesCheck extends ProgramManager with ErrorReporter {

  protected val decreasingFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("decreasing")
  protected val boundedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("bounded")


  protected def createConditionCheck(requiredCondition: Exp, givenCondition: Exp, argMap: Map[LocalVar, Node],
                                     errTrafo: ErrTrafo, reTrafo: ReTrafo): Stmt = {

        val mappedGivenCondition = givenCondition.replace(argMap)

        val implies = Implies(requiredCondition, mappedGivenCondition)(errT = reTrafo)
        Assert(implies)(errT = errTrafo)
  }


  /**
    * Creates checks to determine if the tuple decreases,
    * under the tuple condition of the bigger tuple.
    * If decreasing and bounded functions are not defined a consistency error is reported.
    * @param argMap Substitutions for smallerDec
    * @param errTrafo for termination related assertions
    * @param reasonTrafoFactory for termination related assertion reasons
    * @return termination check as a Assert Stmt (if decreasing and bounded are defined, otherwise EmptyStmt)
    */
  protected def createTupleCheck(biggerTuple: DecreasesTuple, smallerTuple: DecreasesTuple, argMap: Map[LocalVar, Node],
                                 errTrafo: ErrTrafo, reasonTrafoFactory: ReasonTrafoFactory): Stmt = {

    if (decreasingFunc.isEmpty || boundedFunc.isEmpty) {
      if (decreasingFunc.isEmpty){
        reportDecreasingNotDefined(reasonTrafoFactory.offendingNode.pos)
      }
      if (boundedFunc.isEmpty){
        reportBoundedNotDefined(reasonTrafoFactory.offendingNode.pos)
      }
      return EmptyStmt
    }

      // only check decreasing of tuple if the condition is true.
      val callerTupleCondition = biggerTuple.getCondition

      val dtSmall = smallerTuple.tupleExpressions.map(_.replace(argMap))

      val lexCheck = createLexDecreaseCheck(biggerTuple.tupleExpressions, dtSmall, reasonTrafoFactory)

      val decreasesSimpleReasonTrafo = reasonTrafoFactory.generateTupleSimpleFalse()

      val tupleImplies = Implies(callerTupleCondition, lexCheck)(errT = decreasesSimpleReasonTrafo)
      val tupleAssert = Assert(tupleImplies)(errT = errTrafo)

      tupleAssert
  }

  /**
    * Creates Expression checking decreasing and boundedness of the two tuples in lexicographical order.
    * (decreasing(s[0],b[0]) && bounded(b[0])) || (s[0]==b[0] && ( createLexDecreaseCheck(s{1..], b[1..]))
    * Further, both tuples are considered to be extended with a TOP object,
    * which is considered bigger than any other object.
    * If the smallerTuple is empty, false is returned.
    * decreasingFunc and boundedFunc must be defined.
    * @param biggerTuple: tuple do be considered bigger
    * @param smallerTuple: tuple do be considered smaller
    * @return expression or false if smaller expression is empty
    */
  private def createLexDecreaseCheck(biggerTuple: Seq[Exp], smallerTuple: Seq[Exp], reasonTrafoFactory: ReasonTrafoFactory): Exp = {

    assert(decreasingFunc.isDefined)
    assert(boundedFunc.isDefined)

    val simpleReTrafo = reasonTrafoFactory.generateTupleSimpleFalse()
    val decreasesReTrafo = reasonTrafoFactory.generateTupleDecreasesFalse()
    val boundReTrafo = reasonTrafoFactory.generateTupleBoundedFalse()


    val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
    val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)
    val paramTypesBound = boundedFunc.get.formalArgs map (_.typ)
    val argTypeVarsBound = paramTypesBound.flatMap(p => p.typeVariables)

    /**
      * Recursive function to create the check expression
      */
    def createExp(bTuple: Seq[Exp], sTuple: Seq[Exp]): Exp = {
      if(sTuple.isEmpty){
        // smaller tuple would now be appended with TOP
        // TOP cannot be smaller than any expression in the bigger tuple
        FalseLit()(errT = decreasesReTrafo)
      } else if (bTuple.isEmpty) {
        // smaller tuple still has an element
        // bigger tuple would now be appended with TOP
        // any element (besides TOP) is smaller than TOP
        TrueLit()(errT = simpleReTrafo)
      } else {
        // both tuples still have at least one element
        val bigger = bTuple.head
        val smaller = sTuple.head

        if(!(bigger.isSubtype(smaller) || smaller.isSubtype(bigger))){
          // not same types
          FalseLit()(errT = decreasesReTrafo)
        } else {
          // same type

          val dec = DomainFuncApp(decreasingFunc.get,
            Seq(smaller, bigger),
            Map(argTypeVarsDecr.head -> smaller.typ,
              argTypeVarsDecr.last -> bigger.typ))(errT = decreasesReTrafo)

          val bound = DomainFuncApp(boundedFunc.get,
            Seq(bigger),
            ListMap(argTypeVarsBound.head -> bigger.typ,
              argTypeVarsDecr.last -> bigger.typ
            ))(errT = boundReTrafo)

          val andPart = And(dec, bound)(errT = simpleReTrafo)

          val eq = EqCmp(smaller, bigger)(errT = decreasesReTrafo)

          val next = createExp(bTuple.tail, sTuple.tail)
          val nextPart = And(eq, next)(errT = simpleReTrafo)
          Or(andPart, nextPart)(errT = simpleReTrafo)
        }
      }
    }
    createExp(biggerTuple, smallerTuple)
  }

  def reportDecreasingNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Function \"decreasing\" is required but not declared.", pos))
  }

  def reportBoundedNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Function \"bounded\" is required but not defined.", pos))
  }
}