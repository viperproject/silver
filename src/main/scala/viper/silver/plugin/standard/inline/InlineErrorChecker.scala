package viper.silver.plugin.standard.inline

import viper.silver.ast._

trait InlineErrorChecker {

  /**
    * Construct a call-graph of predicates specified by the given predicate ids. If any predicates
    * are found to be (mutually-)recursive, find loop-breakers, a (hopefully minimal) subset of such
    * predicates that can be removed from the call graph so that there is no recursion, and print a
    * warning to the console that they shall not be inlined.
    * Return this set of loop-breakers.
    *
    * @param predicateIds the ids of the predicates we want to inline.
    * @param program the program for which we are performing predicate inlining on.
    * @return the set of mutually-recursive predicates.
    */
  def findLoopBreakers(predicateIds: Set[String], program: Program): Set[String] = {
    val predicateCallGraph = PredicateCallGraph.graph(predicateIds, program)
    val loopBreakers = PredicateCallGraph.loopBreakers(predicateCallGraph)
    if (loopBreakers.nonEmpty) {
      prettyPrint(loopBreakers, "recursion breaking")
    }
    loopBreakers
  }

  private[this] def prettyPrint(preds: Set[String], errorReason: String): Unit = {
    val predIds = preds.mkString(", ")
    if (preds.size > 1) {
      println(s"${Console.YELLOW} [$predIds] are $errorReason predicates and will not be inlined.${Console.RESET}")
    } else {
      println(s"${Console.YELLOW} [$predIds] is a $errorReason predicate and will not be inlined.${Console.RESET}")
    }
  }
}
