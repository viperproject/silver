package viper.silver.plugin.standard.inline

import viper.silver.ast._

trait InlineErrorChecker {

  /**
    * For each predicate id, find its associated body in the program. If the predicate is recursive,
    * print a warning to the console that it shall not be inlined. Return a set of predicates that
    * are recursive.
    *
    * @param predicateIds the ids of the predicates we want to inline.
    * @param program the program for which we are performing predicate inlining on.
    * @return the set of recursive predicates.
    */
  def checkRecursive(predicateIds: Set[String], program: Program): Set[Predicate] = {
    val predicates = predicateIds.map(program.findPredicate)
    val recursivePreds = predicates.filter {
          case Predicate(name, _, maybeBody) => isRecursivePred(name, maybeBody)
    }
    recursivePreds.foreach {
      case Predicate(name, _, _) => println(s"Predicate: `$name` is recursive. Will not be inlined")
    }
    recursivePreds
  }

  /**
    * Construct a call-graph of predicates specified by the given predicate ids. If any predicates
    * are found to be mutually-recursive, print a warning to the console that it shall not be inlined.
    * Return a set of predicates that are mutually-recursive.
    *
    * @param predicateIds the ids of the predicates we want to inline.
    * @param program the program for which we are performing predicate inlining on.
    * @return the set of mutually-recursive predicates.
    */
  def checkMutualRecursive(predicateIds: Set[String], program: Program): Set[Predicate] = {
    val predicatesToInspect = predicateIds.map(program.findPredicate)
    val predicateCallGraph = PredicateCallGraph.graph(predicatesToInspect, program)
    val mutRecPreds = PredicateCallGraph.mutuallyRecursivePreds(predicateCallGraph)
    mutRecPreds.foreach {
      case Predicate(name, _, _) => println(s"Predicate: `$name` is mutually-recursive. Will not be inlined")
    }
    mutRecPreds
  }

  /**
    * Given a predicate id and possibly its body, search the body for a node of type
    * PredicateAccessPredicate(...) with the name identical to the predicate id.
    * If such a node is found, the predicate is recursively defined.
    *
    * @param predId the id for the predicate we want to check for a recursive definition.
    * @param maybePredBody the possible body of the predicate.
    * @return true iff the predicate is found to be recursively defined.
    */
  private[this] def isRecursivePred(predId: String, maybePredBody: Option[Node]): Boolean =
    maybePredBody.fold(false) { predBody =>
      val subNodes = predBody.subnodes
      val existsAtTopLevelNode = subNodes.exists {
        case PredicateAccessPredicate(PredicateAccess(_, name), _) => name == predId
        case _ => false
      }
      val isInChildNodes = subNodes.exists(child => isRecursivePred(predId, Some(child)))
      existsAtTopLevelNode || isInChildNodes
    }
}
