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

  protected var noRecursion = collection.mutable.HashSet.empty[Rewritable[A]]
  protected var wasTransformed = collection.mutable.HashSet.empty[Rewritable[A]]

  def hasChanged = wasTransformed.size > 0

  def transformed(node: Rewritable[A]): Unit = {
    wasTransformed.add(node)
  }

  def dontRecurse(node: Rewritable[A]): Unit = {
    noRecursion.add(node)
  }

  def getTraversionMode = traversionMode



  def traverse(t: Traverse): StrategyInterface[A] = {
    traversionMode = t
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyInterface[A] = {
    recursionFunc = r
    this
  }

  def execute(node: A): A = {
    wasTransformed.clear()
    node
  }

  def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    new ConcatinatedStrategy[A](this, s)
  }

  def repeat: RepeatedStrategy[A] = {
    new RepeatedStrategy[A](this)
  }

  /**
    * Following methods are helper methods for the other Strategy implementations
    */

  protected def recurseChildren(node: A, recurse: A => A): Option[Seq[Any]] = {
    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children = node.getChildren

    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = recursionFunc.applyOrElse(node, (node: A) => {
      children.indices map { x => true }
    })
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length == children.length, "Incorrect number of children in recursion")

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[Any] = children.zip(childrenSelect) map {
      case (o: Option[Rewritable[A]], true) => o match {
        case None => None
        case Some(x: Rewritable[A]) => if (!noRecursion.contains(x)) Some(recurse(x.asInstanceOf[A])) else x
      }
      case (s: Seq[Rewritable[A]], true) => s map { x => if (!noRecursion.contains(x)) recurse(x.asInstanceOf[A]) else x }
      case (n: Rewritable[A], true) => if (!noRecursion.contains(n)) recurse(n.asInstanceOf[A]) else n
      case (old, false) => old
    }


    val hasChanged: Boolean = newChildren.foldLeft(false)((b1, elem) => {
      val b2 = elem match {
        case seq: Seq[Rewritable[A]] => seq.map { wasTransformed.contains(_) }.fold(false)(_ || _)
        case opt: Option[Rewritable[A]] => opt match {
          case Some(x) => wasTransformed.contains(x)
          case None => false // No empty child can be generated from existing child => if None is new child it was already None in old child => no change
        }
        case node: Rewritable[A] => wasTransformed.contains(node)
      }
      b1 || b2
    })

    if (hasChanged) {
      Some(newChildren)
    } else {
      None
    }
  }

}

/**
  * A simple lightweight rewriting strategy
  *
  * @param r A partial function that defines the rewriting.
  * @tparam A Supertype of every node we want to rewrite
  */
class Strategy[A <: Rewritable[A]](val r: PartialFunction[A, A]) extends StrategyInterface[A] {

  val NoContext = new Ancestors[A](Seq(), this) // Just some value because the context is never used

  private var rule: RuleT[A] = Rule(r)

  def getRule: RuleT[A] = {
    rule
  }

  def setRule(r: RuleT[A]) = rule = r

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

  //</editor-fold>

  //<editor-fold desc="Combination Operators">

  def +(s: Strategy[A]): Strategy[A] = {
    rule = Append[A](rule, s.getRule)
    this
  }

  def <(s: Strategy[A]): Strategy[A] = {
    rule = CondAppend[A](rule, s.getRule)
    this
  }

  def ?(s: Strategy[A]): PartialTernary[A] = {
    PartialTernary[A](this, s.getRule)
  }

  def constructRule(s: StrategyInterface[A], Rbuilder: (RuleT[A], RuleT[A]) => RuleT[A]) = {
    s match {
      case s: Strategy[A] =>
        rule = Rbuilder(rule, s.getRule)
      case _ => println("Error: A simple Strategy can only be combined with other simple Strategies")
    }
  }

  //</editor-fold>

  override def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node)
      case Traverse.BottomUp => executeBottomUp(node)
      case Traverse.Innermost => executeInnermost(node)
    }
  }

  def executeTopDown(node: A): A = {
    // Check which node we get from rewriting

    val newNode = rule.execute(node, NoContext).getOrElse(node)

    // Then traverse children and duplicate node with new children
    recurseChildren(newNode, executeTopDown) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }

  def executeBottomUp(node: A): A = {
    // At first recurse into children and get the new children
    val newNode = recurseChildren(node, executeBottomUp) match {
      case Some(children) => node.duplicate(children)
      case None => node
    }

    // Rewrite the node
    rule.execute(newNode, NoContext).getOrElse(newNode)
  }

  def executeInnermost(node: A): A = {
    // Check which node we get from rewriting
    val newNode = rule.execute(node, NoContext).getOrElse(node)

    // Then traverse children
    recurseChildren(newNode, executeTopDown) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }
}


class StrategyA[A <: Rewritable[A]](val r: PartialFunction[(A, Ancestors[A]), A]) extends StrategyInterface[A] {

  private var rule: RuleT[A] = RuleA(r)

  def getRule: RuleT[A] = {
    rule
  }

  def setRule(r: RuleT[A]) = rule = r

  //<editor-fold desc="Overrides for DSL">

  override def traverse(t: Traverse): StrategyA[A] = {
    super.traverse(t)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyA[A] = {
    super.recurseFunc(r)
    this
  }

  //</editor-fold>

  //<editor-fold desc="Combination Operators">

  def +(s: Strategy[A]): StrategyA[A] = {
    rule = Append(rule, s.getRule)
    this
  }

  def +(s: StrategyA[A]): StrategyA[A] = {
    rule = Append(rule, s.getRule)
    this
  }

  def <(s: Strategy[A]): StrategyA[A] = {
    rule = CondAppend(rule, s.getRule)
    this
  }

  def <(s: StrategyA[A]): StrategyA[A] = {
    rule = CondAppend(rule, s.getRule)
    this
  }

  def ?(s: Strategy[A]): PartialTernaryA[A] = {
    PartialTernaryA[A](this, s.getRule)
  }

  def ?(s: StrategyA[A]): PartialTernaryA[A] = {
    PartialTernaryA[A](this, s.getRule)
  }

  //</editor-fold>

  override def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node, new Ancestors[A](Seq(), this))
      case Traverse.BottomUp => executeBottomUp(node, new Ancestors[A](Seq(), this))
      case Traverse.Innermost => executeInnermost(node, new Ancestors[A](Seq(), this))
    }
  }

  def executeTopDown(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node), this)

    // Check which node we get from rewriting
    val newNode = rule.execute(node, newContext).getOrElse(node)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    recurseChildren(newNode, executeTopDown(_, newContext)) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }

  def executeBottomUp(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node), this)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newNode = recurseChildren(node, executeBottomUp(_, newContext)) match {
      case Some(children) => node.duplicate(children)
      case None => node
    }

    rule.execute(newNode, newContext).getOrElse(newNode)
  }

  def executeInnermost(node: A, context: Ancestors[A]): A = {
    // Add this node to context
    val newContext = new Ancestors(context.ancestorList ++ Seq(node), this)

    // Check which node we get from rewriting
    val newNode = rule.execute(node, newContext).getOrElse(node)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    recurseChildren(newNode, executeTopDown(_, newContext)) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }

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

  private var rule: RuleT[A] = RuleC(r)

  def getRule = rule

  def setRule(r: RuleT[A]) = rule = r

  //<editor-fold desc="Overrides for DSL">

  override def traverse(t: Traverse): StrategyC[A, C] = {
    super.traverse(t)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyC[A, C] = {
    super.recurseFunc(r)
    this
  }

  //</editor-fold>

  //<editor-fold desc="Combination Operators">

  def +(s: Strategy[A]): StrategyC[A, C] = {
    rule = Append[A](rule, s.getRule)
    this
  }

  def +(s: StrategyA[A]): StrategyC[A, C] = {
    rule = Append[A](rule, s.getRule)
    this
  }

  def +(s: StrategyC[A, C]): StrategyC[A, C] = {
    rule = Append[A](rule, s.getRule)
    this
  }

  def <(s: Strategy[A]): StrategyC[A, C] = {
    rule = CondAppend[A](rule, s.getRule)
    this
  }

  def <(s: StrategyA[A]): StrategyC[A, C] = {
    rule = CondAppend[A](rule, s.getRule)
    this
  }

  def <(s: StrategyC[A, C]): StrategyC[A, C] = {
    rule = CondAppend[A](rule, s.getRule)
    this
  }

  def ?(s: Strategy[A]): PartialTernaryC[A, C] = {
    PartialTernaryC[A, C](this, s.getRule)
  }

  def ?(s: StrategyA[A]): PartialTernaryC[A, C] = {
    PartialTernaryC[A, C](this, s.getRule)
  }

  def ?(s: StrategyC[A, C]): PartialTernaryC[A, C] = {
    PartialTernaryC[A, C](this, s.getRule)
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
      case Traverse.TopDown => executeTopDown(node, new Context[A, C](Seq(), defaultContxt.get, this))
      case Traverse.BottomUp => executeBottomUp(node, new Context[A, C](Seq(), defaultContxt.get, this))
      case Traverse.Innermost => executeInnermost(node, new Context[A, C](Seq(), defaultContxt.get, this))
    }
  }

  def executeTopDown(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context[A, C](context.ancestorList ++ Seq(node), context.custom, this)

    // Check which node we get from rewriting
    val newNode: A = rule.execute(node, newContext).getOrElse(node)

    // Create the new Context for children recursion
    newContext = new Context(newContext.ancestorList, if (upContext.isDefinedAt(newNode, newContext.custom)) {
      upContext(newNode, context.custom)
    } else {
      newContext.custom
    }, this)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    recurseChildren(newNode, executeTopDown(_, newContext)) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }

  def executeBottomUp(node: A, context: Context[A, C]): A = {
    // Add this node to context
    val newContext = new Context(context.ancestorList ++ Seq(node), if (upContext.isDefinedAt(node, context.custom)) {
      upContext(node, context.custom)
    } else {
      context.custom
    }, this)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newNode = recurseChildren(node, executeBottomUp(_, newContext)) match {
      case Some(children) => node.duplicate(children)
      case None => node
    }

    rule.execute(newNode, newContext).getOrElse(newNode)
  }

  def executeInnermost(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context(context.ancestorList ++ Seq(node), context.custom, this)

    // Check which node we get from rewriting
    val newNode: A = rule.execute(node, newContext).getOrElse(node)

    // Create the new Context for children recursion
    newContext = new Context(newContext.ancestorList, if (upContext.isDefinedAt(newNode, newContext.custom)) {
      upContext(newNode, context.custom)
    } else {
      newContext.custom
    }, this)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    recurseChildren(newNode, executeTopDown(_, newContext)) match {
      case Some(children) => newNode.duplicate(children)
      case None => newNode
    }
  }
}

/**
  * This class encapsulates strategies that are appended. The execute method executes them one after another and gives the resulting node of a transformation
  * as an argument for the next node
  *
  * @param s1 strategy 1
  * @param s2 strategy 2
  */
class ConcatinatedStrategy[A <: Rewritable[A]](s1: StrategyInterface[A], val s2: StrategyInterface[A]) extends StrategyInterface[A] {
  private var strategies = collection.mutable.ListBuffer.empty[StrategyInterface[A]]

  strategies.append(s1)
  strategies.append(s2)


  override def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    strategies.append(s)
    this
  }

  def ||(s: ConcatinatedStrategy[A]): ConcatinatedStrategy[A] = {
    strategies ++= s.strategies
    this
  }

  override def execute(node: A): A = strategies.foldLeft(node)((n, strat) => strat.execute(n))
}

class RepeatedStrategy[A <: Rewritable[A]](s: StrategyInterface[A]) extends StrategyInterface[A] {
  override def execute(node: A): A = {
    val result = s.execute(node)
    if (s.hasChanged) {
      result
    } else {
      execute(result)
    }
  }

  def execute(node: A, i: Int): A = {
    if (i <= 0) node

    val result = s.execute(node)
    if (s.hasChanged) {
      result
    } else {
      execute(result, i - 1)
    }
  }
}

/**
  * This class holds ancestor information about the current node
  *
  * @param ancestorList List of all ancestors
  */
class Ancestors[A <: Rewritable[A]](val ancestorList: Seq[A], val transformer: StrategyInterface[A]) {

  private[utility] def newNode(node: A): Ancestors[A] = {
    new Ancestors[A](ancestorList.dropRight(1) ++ Seq(node), transformer)
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
  lazy val family: Seq[Any] = parent.getChildren.foldLeft(Seq.empty[Any])((children: Seq[Any], y: Any) => y match {
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
  * This class works as a Tuple of a custom context and an ancestor list. It extends Ancestors such that we get: RuleC < RuleA < Rule
  *
  * @param aList  List from the Ancestors part
  * @param custom Custom context part
  */
class Context[A <: Rewritable[A], C](aList: Seq[A], val custom: C, transformer: StrategyInterface[A]) extends Ancestors[A](aList, transformer) {
  override def newNode(node: A): Context[A, C] = {
    new Context(ancestorList.dropRight(1) ++ Seq(node), custom, transformer)
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
    val children = node.getChildren


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
  * RuleC < RuleA < Rule that proves helpful when combining those rules
  */
private[utility] trait RuleT[A <: Rewritable[A]] {
  def execute(node: A, context: Ancestors[A]): Option[A]
}

/**
  * RuleC lifts a partial function to a rule that is used in StrategyC
  *
  * @param r The partial function
  */
private case class RuleC[A <: Rewritable[A], C](r: PartialFunction[(A, Context[A, C]), A]) extends RuleT[A] {
  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    if (r.isDefinedAt((node, context.asInstanceOf[Context[A, C]]))) {
      val res = r((node, context.asInstanceOf[Context[A, C]]))
      res.setTransformed(true)
      Some(res)
    } else {
      None
    }
  }
}

/**
  * RuleA lifts a partial function to a rule that is used in a StrategyA
  *
  * @param r The partial function
  */
private case class RuleA[A <: Rewritable[A]](r: PartialFunction[(A, Ancestors[A]), A]) extends RuleT[A] {
  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    if (r.isDefinedAt((node, context))) {
      val res = r((node, context))
      res.setTransformed(true)
      Some(res)
    } else {
      None
    }
  }
}

/**
  * Rule lifts a partial function to a rule that is used in a Strategy
  *
  * @param r The partial function
  */
private case class Rule[A <: Rewritable[A]](r: PartialFunction[A, A]) extends RuleT[A] {

  def execute(node: A): Option[A] = {
    execute(node, new Ancestors[A](Nil, new Strategy[A](PartialFunction.empty[A,A]))) // Just put in any parameter. it will not be used anyways
  }

  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    if (r.isDefinedAt(node)) {
      val res = r(node)
      res.setTransformed(true)
      Some(res)
    } else {
      None
    }
  }
}

/**
  * Class Append takes two rules and executes them one after another
  *
  * @param r1 First rule
  * @param r2 Second rule
  */
private case class Append[A <: Rewritable[A]](r1: RuleT[A], r2: RuleT[A]) extends RuleT[A] {

  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.newNode(res1.get))
      if (res2.isDefined) res2 else res1
    } else {
      r2.execute(node, context)
    }
  }
}

/**
  * CondAppend takes two rules as parameter. If r1 is defined on a node it will execute both otherwise nothing
  *
  * @param r1 First rule
  * @param r2 Second rule
  *
  */
private case class CondAppend[A <: Rewritable[A]](r1: RuleT[A], r2: RuleT[A]) extends RuleT[A] {

  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.newNode(res1.get))
      if (res2.isDefined) res2 else res1
    }
    else {
      None
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
private case class Ternary[A <: Rewritable[A]](r1: RuleT[A], r2: RuleT[A], r3: RuleT[A]) extends RuleT[A] {

  override def execute(node: A, context: Ancestors[A]): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.newNode(node))
      if (res2.isDefined) res2 else res1
    } else {
      val res3 = r3.execute(node, context)
      if (res3.isDefined) res3 else res1
    }
  }
}

// Three partial ternary classes one for each strategy to make it typesafe
case class PartialTernary[A <: Rewritable[A]](s: Strategy[A], r2: RuleT[A]) {
  def |(s2: Strategy[A]): Strategy[A] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }
}

case class PartialTernaryA[A <: Rewritable[A]](s: StrategyA[A], r2: RuleT[A]) {
  def |(s2: Strategy[A]): StrategyA[A] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }

  def |(s2: StrategyA[A]): StrategyA[A] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }
}

case class PartialTernaryC[A <: Rewritable[A], C](s: StrategyC[A, C], r2: RuleT[A]) {
  def |(s2: Strategy[A]): StrategyC[A, C] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }

  def |(s2: StrategyA[A]): StrategyC[A, C] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }

  def |(s2: StrategyC[A, C]): StrategyC[A, C] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }
}