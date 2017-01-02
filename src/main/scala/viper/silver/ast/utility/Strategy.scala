package viper.silver.ast.utility

import viper.silver.ast.utility.Traverse.Traverse

/**
  * Created by simonfri on 05.12.2016.
  */

/**
  * An enumeration that represents traversion modes:
  * - TopDown: Perform transformation before visiting children
  * - BottomUp: Perform transformation after visiting children
  * - Innermost: Go TopDown but stop recursion after first rewrite
  * - Outermost: Go BottomUp and only rewrite first match
  */
object Traverse extends Enumeration {
  type Traverse = Value
  val TopDown, BottomUp, Innermost, Outermost = Value
}

/**
  * Trait that encapsulates all fields and Setter/Getter that are used in every Strategy
  *
  * @tparam A with Rewritable[A][N] Supertype of every node we want to rewrite
  */
trait StrategyInterface[A <: Rewritable[A]] {

  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty

  def getTraversionMode = traversionMode

  def traverse(t: Traverse): StrategyInterface[A] = {
    traversionMode = t
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyInterface[A] = {
    recursionFunc = r
    this
  }

  def execute(node: A): A

  def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    new ConcatinatedStrategy[A](this, s)
  }

  /**
    * Following methods are helper methods for the other Strategy implementations
    */

  protected def recurseChildren(node: A, recurse: A =>A): Seq[Any] = {
    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children = node.getChildren()

    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = recursionFunc.applyOrElse(node, (node: A) => {
      children.indices map { x => true }
    })
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length == children.length, "Incorrect number of children in recursion")

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[Any] = children.zip(childrenSelect) map {
      case (child, b) => if (b) {
        child match {
          case o: Option[Rewritable[A]] => o match {
            case None => Nil
            case Some(x: Rewritable[A]) => Some(recurse(x.asInstanceOf[A]))
          }
          case s: Seq[Rewritable[A]] => s map { x => recurse(x.asInstanceOf[A]) }
          case n: Rewritable[A] => recurse(n.asInstanceOf[A])
        }
      } else {
        child
      }
    }
    newChildren
  }

}

/**
  * A simple lightweight rewriting strategy
  *
  * @param r A partial function that defines the rewriting.
  * @tparam A Supertype of every node we want to rewrite
  */
class Strategy[A <: Rewritable[A]](val r: PartialFunction[A, A]) extends StrategyInterface[A] {

  val NoContext = new Ancestors[A](Seq()) // Just some value because the context is never used

  private var rule: Rule[A] = RuleS(r)

  def getRule: Rule[A] = {
    rule
  }

  //<editor-fold desc="Overrides for DSL">

  // We need to override all the setters beacuse we want to return a Strategy and not a Strategy interface
  // for DSL purposes. Otherwise we wont be able to call Strategy only functions
  override def traverse(t: Traverse): Strategy[A] = {
    super.traverse(t)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Strategy[A] = {
    super.recurseFunc(r)
    this
  }


  def +(s: StrategyInterface[A]): Strategy[A] = {
    s match {
      case s: Strategy[A] =>
        rule = Append[A](rule, s.rule)
      case _ => println("Error: A simple Strategy can only be combined with other simple Strategies")
    }
    this
  }

  def <(s: StrategyInterface[A]): Strategy[A] = {
    s match {
      case s: Strategy[A] =>
        rule = CondAppend[A](rule, s.rule)
      case _ => println("Error: A simple Strategy can only be combined with other simple Strategies")
    }
    this
  }

  //</editor-fold>

  override def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node)
      case Traverse.BottomUp => executeBottomUp(node)
      case Traverse.Innermost => executeInnermost(node)
      case Traverse.Outermost => executeOutermost(node)
    }
  }

  def executeTopDown(node: A): A = {

    // Check which node we get from rewriting
    val newNode = rule.execute(node, NoContext)

    // Then traverse children
    val newChildren: Seq[Any] = recurseChildren(newNode, executeTopDown)
    //println(newChildren map { x => x.getClass })
    // Duplicate node with new children as children
    newNode.duplicate(newChildren)
  }

  def executeBottomUp(node: A): A = {

    // At first recurse into children and get the new children
    val newChildren: Seq[Any] = recurseChildren(node, executeBottomUp)

    val duplicatedNode: A = node.duplicate(newChildren)

    // Rewrite the node
    rule.execute(duplicatedNode, NoContext)
  }

  def executeInnermost(node: A): A = {
    // Check which node we get from rewriting
    val newNode = rule.execute(node, NoContext)

    // Then traverse children
    val newChildren: Seq[Any] = recurseChildren(newNode, executeTopDown)
    //println(newChildren map { x => x.getClass })
    // Duplicate node with new children as children
    newNode.duplicate(newChildren)
  }

  def executeOutermost(node: A): A = ???

}


class StrategyA[A <: Rewritable[A]](val r: PartialFunction[(A, Ancestors[A]), A]) extends StrategyInterface[A] {
  //<editor-fold desc="Overrides for DSL">

  private var rule: Rule[A] = RuleA(r)

  def getRule: Rule[A] = {
    rule
  }

  override def traverse(t: Traverse): StrategyA[A] = {
    super.traverse(t)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyA[A] = {
    super.recurseFunc(r)
    this
  }

  def +(s: StrategyInterface[A]): StrategyA[A] = {
    s match {
      case s: Strategy[A] =>
        rule = Append[A](rule, s.getRule)
      case a: StrategyA[A] =>
        rule = Append[A](rule, a.rule)
      case _ => println("Error: A StrategyA can only be combined with simple Strategies or other StrategyAs")
    }
    this
  }

  def <(s: StrategyInterface[A]): StrategyA[A] = {
    s match {
      case s: Strategy[A] =>
        rule = CondAppend[A](rule, s.getRule)
      case a: StrategyA[A] =>
        rule = CondAppend[A](rule, a.rule)
      case _ => println("Error: A StrategyA can only be combined with simple Strategies or other StrategyAs")
    }
    this
  }

  override def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node, new Ancestors[A](Seq()))
      case Traverse.BottomUp => executeBottomUp(node, new Ancestors[A](Seq()))
      case Traverse.Innermost => executeInnermost(node, new Ancestors[A](Seq()))
      case Traverse.Outermost => executeOutermost(node, new Ancestors[A](Seq()))
    }
  }

  def executeTopDown(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node))

    // Check which node we get from rewriting
    val newNode: A = if (r.isDefinedAt((node, newContext))) {
      r((node, newContext))
    } else {
      node
    }

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    newNode.duplicate(newChildren)
  }

  def executeBottomUp(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node))

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(node, executeBottomUp(_, newContext))

    val newNode = node.duplicate(newChildren)

    if (r.isDefinedAt((newNode, newContext))) {
      r((newNode, newContext))
    } else {
      newNode
    }
  }

  def executeInnermost(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node))

    // Check which node we get from rewriting
    val newNode: A = if (r.isDefinedAt((node, newContext))) {
      return r((node, newContext))
    } else {
      node
    }

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    newNode.duplicate(newChildren)
  }

  def executeOutermost(node: A, context: Ancestors[A]): A = ???


}


/**
  * A strategy that provides a context during rewriting. The user can control what is in the context by providing a updateContext method
  * that will be called for every ancestor of the node
  *
  * @param r A partial function that describes the rewriting. It takes the candidate node for rewriting and the context as argument and delivers a rewritten node
  * @tparam A Supertype of every node we want to rewrite
  * @tparam C Supertype of the context
  */
class StrategyC[A <: Rewritable[A], C](val r: PartialFunction[(A, Context[A, C]), A]) extends StrategyInterface[A] {
  protected var upContext: PartialFunction[(A, C), C] = PartialFunction.empty
  protected var defaultContxt: Option[C] = None

  private var rule: Rule[A] = RuleC(r)

  //<editor-fold desc="Overrides for DSL">

  override def traverse(t: Traverse): StrategyC[A, C] = {
    super.traverse(t)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyC[A, C] = {
    super.recurseFunc(r)
    this
  }

  def +(s: StrategyInterface[A]): StrategyC[A, C] = {
    s match {
      case s: Strategy[A] =>
        rule = Append[A](rule, s.getRule)
      case a: StrategyA[A] =>
        rule = Append[A](rule, a.getRule)
      case c: StrategyC[A, C] =>
        rule = Append[A](rule, c.rule)
      case _ => println("Error: A StrategyC can only be combined with simple Strategies, StrategyAs or StrategyCs")
    }
    this
  }

  def <(s: StrategyInterface[A]): StrategyC[A, C] = {
    s match {
      case s: Strategy[A] =>
        rule = CondAppend[A](rule, s.getRule)
      case a: StrategyA[A] =>
        rule = CondAppend[A](rule, a.getRule)
      case _ => println("Error: A StrategyC can only be combined with simple Strategies, StrategyAs or StrategyCs")
    }
    this
  }

  //</editor-fold>

  def updateContext(p: PartialFunction[(A, C), C]): StrategyC[A, C] = {
    upContext = p
    this
  }

  def defaultContext(c: C): StrategyC[A, C] = {
    defaultContxt = Some(c)
    this
  }

  override def execute(node: A): A = {
    assert(defaultContxt.isDefined, "Default context not set!")
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node, new Context[A, C](Seq(), defaultContxt.get))
      case Traverse.BottomUp => executeBottomUp(node, new Context[A, C](Seq(), defaultContxt.get))
      case Traverse.Innermost => executeInnermost(node, new Context[A, C](Seq(), defaultContxt.get))
      case Traverse.Outermost => executeOutermost(node, None)
    }
  }

  def executeTopDown(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context[A, C](context.ancestorList ++ Seq(node), context.custom)

    // Check which node we get from rewriting
    val newNode: A = if (r.isDefinedAt((node, newContext))) {
      r((node, newContext))
    } else {
      node
    }

    // Create the new Context for children recursion
    newContext = new Context(newContext.ancestorList, if (upContext.isDefinedAt(newNode, newContext.custom)) {
      upContext(newNode, context.custom)
    } else {
      newContext.custom
    })

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    newNode.duplicate(newChildren)
  }

  def executeBottomUp(node: A, context: Context[A, C]): A = {
    // Add this node to context
    val newContext = new Context(context.ancestorList ++ Seq(node), if (upContext.isDefinedAt(node, context.custom)) {
      upContext(node, context.custom)
    } else {
      context.custom
    })

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(node, executeBottomUp(_, newContext))

    val newNode = node.duplicate(newChildren)

    if (r.isDefinedAt((newNode, newContext))) {
      r((newNode, newContext))
    } else {
      newNode
    }
  }

  def executeInnermost(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context(context.ancestorList ++ Seq(node), context.custom)

    // Check which node we get from rewriting
    val newNode: A = if (r.isDefinedAt((node, newContext))) {
      return r((node, newContext))
    } else {
      node
    }

    // Create the new Context for children recursion
    newContext = new Context(newContext.ancestorList, if (upContext.isDefinedAt(newNode, newContext.custom)) {
      upContext(newNode, context.custom)
    } else {
      newContext.custom
    })

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    newNode.duplicate(newChildren)
  }

  def executeOutermost(node: A, context: Option[C]): A = ???


}

/**
  * This class encapsulates strategies that are appended. The execute method executes them one after another and gives the resulting node of a transformation
  * as an argument for the next node
  * @param s1 strategy 1
  * @param s2 strategy 2
  */
class ConcatinatedStrategy[A <: Rewritable[A]](s1: StrategyInterface[A], val s2: StrategyInterface[A]) {
  strategies.append(s1)
  strategies.append(s2)

  private var strategies = collection.mutable.ListBuffer.empty[StrategyInterface[A]]

  def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    strategies.append(s)
    this
  }

  def ||(s: ConcatinatedStrategy[A]): ConcatinatedStrategy[A] = {
    strategies ++= s.strategies
    this
  }

  def execute(node: A): A = strategies.foldLeft(node)( (n, strat) => strat.execute(n) )
}

/**
  * This class holds ancestor information about the current node
  * @param ancestorList List of all ancestors
  */
class Ancestors[A <: Rewritable[A]](val ancestorList: Seq[A]) {

  private[utility] def newNode(node: A): Ancestors[A] = {
    new Ancestors[A](ancestorList.dropRight(1) ++ Seq(node))
  }

  lazy val node = ancestorList.last

  /**
    * The predecessor child of the parent that follows the node itself
    */
  lazy val previous: Option[Any] = predecessors.lastOption

  /**
    * All children of the parent of a node that precede the node itself
    */
  lazy val predecessors: Seq[Any] = family.takeWhile(!isEqualNode(_))

  /**
    * The successor child of the parent that follows the node itself
    */
  lazy val next: Option[Any] = successors.headOption

  /**
    * All children of the parent of a node that follow the node itself
    */
  lazy val successors: Seq[Any] = family.dropWhile(!isEqualNode(_)).drop(1)


  /**
    * All children of the parent without the node itself
    */
  lazy val siblings: Seq[Any] = family.filter(!isEqualNode(_))


  /**
    * All children of the parent. Sequence of nodes and options of nodes will be unfolded and the node itself is included in the list
    */
  lazy val family: Seq[Any] = parent.getChildren().foldLeft(Seq.empty[Any])((children: Seq[Any], y: Any) => y match {
    case elem: Seq[A] => children ++ elem
    case elem: Option[A] => children ++ (elem match {
      case Some(x) => Seq(x)
      case None => Seq.empty[Any]
    })
    case elem => children ++ Seq(elem)
  })
  /**
    * Parent of node
    */
  lazy val parent: A = ancestorList.dropRight(1).last

  def isEqualNode(elem: Any): Boolean = elem match {
    case Some(x: AnyRef) => x eq node.asInstanceOf[AnyRef]
    case Seq(_) => false
    case p: AnyRef => p eq node.asInstanceOf[AnyRef]
  }
}

/**
  * This class works as a Tuple of a custom context and an ancestor list. It extends Ancestors such that we get: RuleC < RuleA < RuleS
  * @param aList List from the Ancestors part
  * @param custom Custom context part
  */
class Context[A <: Rewritable[A], C](aList: Seq[A], val custom: C) extends Ancestors[A](aList) {
  override def newNode(node: A): Context[A, C] = {
    new Context(ancestorList.dropRight(1) ++ Seq(node) , custom)
  }
}


class Query[A <: Rewritable[A], B](val getInfo: PartialFunction[A, B]) {

  protected var accumulator: Seq[B] => B = (x: Seq[B]) => x.head
  protected var nElement: Option[B] = None

  def getAccumulator = accumulator

  def accumulate(a: Seq[B] => B): Query[A, B] = {
    accumulator = a
    this
  }
  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty

  def getTraversionMode = traversionMode

  def getNeutralElement = nElement

  def neutralElement(ne: B): Query[A, B] = {
    nElement = Some(ne)
    this
  }

  def traverse(t: Traverse): Query[A, B] = {
    traversionMode = t
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Query[A, B] = {
    recursionFunc = r
    this
  }

  // Query only makes sense top down
  def execute(node: A): B = {
    // Check which node we get from rewriting
    val qResult: B = if (getInfo.isDefinedAt(node)) {
      getInfo(node)
    } else {
      assert(nElement.isDefined, "Node " + node + "does not define a result. Either define it in query or specify neutral element")
      nElement.get
    }

    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children = node.getChildren()


    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = if (recursionFunc.isDefinedAt(node)) {
      recursionFunc(node)
    } else {
      children.indices map { x => true }
    }
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length == children.length, "Incorrect number of children in recursion")


    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val seqResults: Seq[Option[B]] = children.zip(childrenSelect) collect {
      case (child, b) => if (b) {
        child match {
          case o: Option[Rewritable[A]] => o match {
            case None => None
            case Some(node: Rewritable[A]) => Some(execute(node.asInstanceOf[A]))
          }
          case s: Seq[Rewritable[A]] => Some(accumulator(s map { x => execute(x.asInstanceOf[A]) }))
          case n: Rewritable[A] => Some(execute(n.asInstanceOf[A]))
        }
      } else {
        None
      }
    }
    accumulator(Seq(qResult) ++ (seqResults collect { case Some(x: B) => x }))
  }

}


// ------------------------------------------------------------------------- Composition Code here -------------------------------------------------------------------------------------------------

/**
  * A trait that is used for providing an interface for rules. We need the contravariance parameter to create the relationship:
  * RuleC < RuleA < RuleS that proves helpful when combining those rules
  */
private[utility] trait Rule[A <: Rewritable[A]] {
  def execute(node: A, context: Ancestors[A]): A
}

/**
  * RuleC lifts a partial function to a rule that is used in StrategyC
  * @param r The partial function
  */
private case class RuleC[A <: Rewritable[A], C](r: PartialFunction[(A, Context[A, C]), A]) extends Rule[A] {
  override def execute(node: A, context: Ancestors[A]): A = {
    if (r.isDefinedAt((node, context.asInstanceOf[Context[A,C]]))) {
      r((node, context.asInstanceOf[Context[A,C]]))
    } else {
      node
    }
  }
}

/**
  * RuleA lifts a partial function to a rule that is used in a StrategyA
  * @param r The partial function
  */
private case class RuleA[A <: Rewritable[A]](r: PartialFunction[(A, Ancestors[A]), A]) extends Rule[A] {
  override def execute(node: A, context: Ancestors[A]): A = {
    if (r.isDefinedAt((node, context))) {
      r((node, context))
    } else {
      node
    }
  }
}

/**
  * RuleS lifts a partial function to a rule that is used in a Strategy
  * @param r The partial function
  */
private case class RuleS[A <: Rewritable[A]](r: PartialFunction[A, A]) extends Rule[A] {

  def execute(node: A): A = {
    execute(node, new Ancestors[A](Nil)) // Just put in any parameter. it will not be used anyways
  }

  override def execute(node: A, context: Ancestors[A]): A = {
    if (r.isDefinedAt(node)) {
      r(node)
    } else {
      node
    }
  }
}

/**
  * Class Append takes two rules and executes them one after another
  * @param r1 First rule
  * @param r2 Second rule
  */
private case class Append[A <: Rewritable[A]](r1: Rule[A], r2: Rule[A]) extends Rule[A] {

  override def execute(node: A, context: Ancestors[A]): A = {
    val res1 = r1.execute(node, context)
    if(res1 ne node) {
      r2.execute(res1, context.newNode(res1))
    } else {
      r2.execute(res1, context)
    }
  }
}

/**
  * CondAppend takes two rules as parameter. If r1 is defined on a node it will execute both otherwise nothing
  * @param r1 First rule
  * @param r2 Second rule
  *
  */
private case class CondAppend[A <: Rewritable[A]](r1: Rule[A], r2: Rule[A]) extends Rule[A] {

  override def execute(node: A, context: Ancestors[A]): A = {
    val res1 = r1.execute(node, context)
    if (res1 ne node) {
      r2.execute(res1, context.newNode(res1))
    }
    else {
      node
    }
  }
}

/**
  * Ternary takes three rules as parameter. If r1 is defined on a node it will execute r1 and r2 otherwise r3
  *
  * @param r1 Rule for condition
  * @param r2 Rule in case defined
  * @param r3 Rule in case not defined
  */
private case class Ternary[A <: Rewritable[A]](r1: Rule[A], r2: Rule[A], r3: Rule[A]) extends Rule[A] {

  override def execute(node: A, context: Ancestors[A]): A = {
    val res1 = r1.execute(node, context)
    if (res1 ne node) {
      r2.execute(res1, context.newNode(node))
    } else {
      r3.execute(node, context)
    }
  }
}