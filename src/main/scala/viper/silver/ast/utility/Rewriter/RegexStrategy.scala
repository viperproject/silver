package viper.silver.ast.utility.Rewriter

// Extension of the Strategy context. Encapsulates all the required information for the rewriting
// aList: List of all the ancestors
// c: context information
// t: the transformer we run on
// upContext: Function that describes how we update the context in case new context information comes in
// comp: Function that evaluates which context to take in case a node is in two possible contexts at the same time (true = first param, false = second param)
class RegexContext[A <: Rewritable, COLL](aList: Seq[A], val c: COLL, transformer: StrategyInterface[A], val upContext: (COLL, COLL) => COLL, val comp: (COLL, COLL) => Boolean) extends ContextA[A](aList, transformer) {

  // Add an ancestor
  override def addAncestor(n: A): RegexContext[A, COLL] = {
    new RegexContext(ancestorList ++ Seq(n), c, transformer, upContext, comp)
  }

  // Replace the current node
  override def replaceNode(n: A): RegexContext[A, COLL] = {
    new RegexContext(ancestorList.dropRight(1) ++ Seq(n), c, transformer, upContext, comp)
  }

  // Update the context with new information
  def update(con: COLL): RegexContext[A, COLL] = {
    new RegexContext(ancestorList, upContext(c, con), transformer, upContext, comp)
  }

  // Compare the context in order decide which one to take
  def compare(other: RegexContext[A, COLL]): Boolean = {
    comp(this.c, other.c)
  }
}

// A class that misses some information in order to be a full RegexContext. Provides methods to create a complete one
class PartialContextR[A <: Rewritable, COLL](val c: COLL, val upContext: (COLL, COLL) => COLL, val comp: (COLL, COLL) => Boolean) extends PartialContext[A, ContextA[A]] {

  def get(anc: Seq[A], transformer: StrategyInterface[A]): RegexContext[A, COLL] = new RegexContext[A, COLL](anc, c, transformer, upContext, comp)

  override def get(transformer: StrategyInterface[A]): RegexContext[A, COLL] = new RegexContext[A, COLL](Seq(), c, transformer, upContext, comp)
}

// A class that helps with providing dummy context in a rewriting function. Used to make SlimRegexStrategy compatible with RegexStrategy
case class SimpleRegexContext[N <: Rewritable](p: PartialFunction[N, N]) extends PartialFunction[(N, RegexContext[N, Any]), N] {
  override def isDefinedAt(x: (N, RegexContext[N, Any])): Boolean = p.isDefinedAt(x._1)

  override def apply(x: (N, RegexContext[N, Any])): N = p.apply(x._1)
}

// A regex strategy that does not include context (convenience)
class SlimRegexStrategy[N <: Rewritable](a: TRegexAutomaton, p: PartialFunction[N, N]) extends RegexStrategy[N, Any](a, SimpleRegexContext(p), new PartialContextR(null, (x, y) => x, (x, y) => true))

// A strategy that performs rewriting according to the Regex and Rewriting function specified
// a: The automaton generated from the regular expression
// p: PartialFunction that describes rewriting
// default: The context we start with
class RegexStrategy[N <: Rewritable, COLL](a: TRegexAutomaton, p: PartialFunction[(N, RegexContext[N, COLL]), N], default: PartialContextR[N, COLL]) extends Strategy[N, RegexContext[N, COLL]](p) {

  type CTXT = RegexContext[N, COLL]

  // Custom data structure for keeping the node context pairs
  class MatchSet {
    var map = collection.mutable.ListBuffer.empty[(N, CTXT)]

    // Put a new tuple into the data structure. If an entry for the node already exists keep the tuple with bigger context according to the regex context
    def put(tuple: (N, CTXT)) = {
      val node = tuple._1
      val context = tuple._2
      map.zipWithIndex.find(_._1._1 eq node) match {
        case None => map.append((node, context))
        case Some(tup) =>
          val better = (node, if (tup._1._2.compare(context)) tup._1._2 else context)
          map.remove(tup._2)
          map.append(better)
      }
    }

    // Get the tuple that matches parameter node
    def get(node: N): Option[CTXT] = {
      map.find(_._1 eq node) match {
        case None => None
        case Some(t) => Some(t._2)
      }
    }

  }

  // Execute the rewriting
  override def execute[T <: N](node: N): T = {
    wasTransformed.clear()

    // Store found matches here
    val matches = new MatchSet

    // Recursively matches on the AST by iterating through the automaton
    def recurse(n: N, s: State, ctxt: CTXT, marked: Seq[(N, CTXT)]): Unit = {

      // Perform possible transition and obtain actions.
      // If no transition is possible (error state) states will be empty after this call and the recursion will stop
      val (states, action) = s.performTransition(n)

      // Get all the children to recurse further
      val children: Seq[Rewritable] = n.getChildren.foldLeft(Seq.empty[Rewritable])({
        case (seq, o: Option[Rewritable]) => o match {
          case None => seq
          case Some(x: Rewritable) => seq ++ Seq(x)
        }
        case (seq, s: Seq[Rewritable]) => seq ++ s
        case (seq, r: Rewritable) => seq ++ Seq(r)
        case (seq, _) => seq
      })

      // Actions may or may not change marked nodes, children or context
      var newMarked = marked
      var newChildren = children
      var newCtxt = ctxt.addAncestor(n)

      // Apply actions
      action foreach {
        // Marked for rewrite TODO: error handling in case node casting fails
        case MarkedForRewrite() => newMarked = newMarked ++ Seq((n.asInstanceOf[N], newCtxt))
        // Context update TODO: error handling in case context casting fails
        case ContextInfo(c: Any) => newCtxt = ctxt.update(c.asInstanceOf[COLL])
        // Only recurse if we are the selected child
        case ChildSelectInfo(r: Rewritable) => newChildren.filter(_ eq r)
      }

      // If we reach an accepting state put it into matches
      if (states.exists(_.isAccepting)) {
        newMarked.foreach(matches.put)
      }


      // Perform further recursion for each child and for each state that is not already accepting
      newChildren.foreach(child => {
        states.filter(!_.isAccepting).foreach(state => {
          recurse(child.asInstanceOf[N], state, newCtxt, newMarked)
        })
      })
    }

    // Use the recurse function to find every sub patch that satisfied the regular expression and fill variable matches with all the nodes marked for rewriting

    // Efficiency: Only start if the first match matches
    val startStates = a.start.effective
    val visitor = StrategyBuilder.AncestorStrategy[N]({ case (n, c) => {
      // Start recursion if any of the start states is valid for recursion
      startStates.foreach(s => {
        if (s.isValidInput(n))
          recurse(n, s, default.get(c.ancestorList.dropRight(1), this), Seq.empty[(N, CTXT)])
      })
      n
    }
    })

    visitor.execute(node)

    val result = replaceTopDown(node, matches)
    result.asInstanceOf[T]
  }

  // Replace the marked nodes with the transformed nodes
  def replaceTopDown(n: N, matches: MatchSet): N = {
    // Find out if this node is going to be replaced
    val replaceInfo = matches.get(n)

    // get resulting node from rewriting
    val resultNode = replaceInfo match {
      case None => n
      case Some(elem) =>
        if (p.isDefinedAt(n, elem))
          transformed(p(n, elem))
        else
          n
    }

    // Recurse into children
    val res = recurseChildren(resultNode, replaceTopDown(_, matches)) match {
      case Some(children) => transformed(resultNode.duplicate(children).asInstanceOf[N])
      case None => resultNode
    }

    // Call preserve metadata to allow possible extensions to do their work
    preserveMetaData(n, res)
  }
}