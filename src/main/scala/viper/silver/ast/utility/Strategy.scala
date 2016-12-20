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
  * @tparam A Supertype of every node we want to rewrite
  */
trait StrategyInterface[A] {

  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty
  protected var cChildren: PartialFunction[A, Seq[A]] = PartialFunction.empty
  protected var duplicator: PartialFunction[(A, Seq[Any]), A] = PartialFunction.empty

  def getTraversionMode = traversionMode

  def traverse(t: Traverse): StrategyInterface[A] = {
    traversionMode = t
    this
  }

  def getcustomChildren = cChildren

  def customChildren(c: PartialFunction[A, Seq[A]]): StrategyInterface[A] = {
    cChildren = c
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyInterface[A] = {
    recursionFunc = r
    this
  }

  def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): StrategyInterface[A] = {
    duplicator = d
    this
  }

  def execute(node: A): Any

  /**
    * Following methods are helper methods for the other Strategy implementations
    */

  protected def recurseChildren(node: A, recurse:Function1[A, A]): Seq[Any] = {
    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children: Seq[Any] = cChildren.applyOrElse(node, (x: A) => x match {
      case p: Product => ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
        case s: Seq[Product] => s
        case o: Option[Product] => o
        case i: Product => i.asInstanceOf[A]
      }
      case rest =>
        println("We do not support nodes that dont implement product")
        Seq()
    })

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
          case o: Option[Product] => o match {
            case None => None
            case Some(node: Product) => Some(recurse(node.asInstanceOf[A]))
          }
          case s: Seq[Product] => s map { x => recurse(x.asInstanceOf[A]) }
          case n: Product => recurse(n.asInstanceOf[A])
          case rest => rest
        }
      } else {
        child
      }
    }
    newChildren
  }

  protected def tryDuplicate(node: A, newChildren:Seq[Any]): A = {
    // Create a new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    if (duplicator.isDefinedAt((node, newChildren.asInstanceOf[Seq[Any]]))) {
      duplicator((node, newChildren.asInstanceOf[Seq[Any]]))
    } else {
      node
    }
  }
}

/**
  * A simple lightweight rewriting strategy
  *
  * @param rule A partial function that defines the rewriting.
  * @tparam A Supertype of every node we want to rewrite
  */
class Strategy[A](val rule: PartialFunction[A, A]) extends StrategyInterface[A] {

  //<editor-fold desc="Overrides for DSL">

  // We need to override all the setters beacuse we want to return a Strategy and not a Strategy interface
  // for DSL purposes. Otherwise we wont be able to call Strategy only functions
  override def traverse(t: Traverse): Strategy[A] = {
    super.traverse(t)
    this
  }

  override def customChildren(r: PartialFunction[A, Seq[A]]): Strategy[A] = {
    super.customChildren(r)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Strategy[A] = {
    super.recurseFunc(r)
    this
  }

  override def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): Strategy[A] = {
    super.defineDuplicator(d)
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
    // TODO Replace printouts with actual exceptions

    // Check which node we get from rewriting
    val newNode = if (rule.isDefinedAt(node)) {
      rule(node)
    } else {
      node
    }

    // Then traverse children
    val newChildren: Seq[Any] = recurseChildren(newNode, executeTopDown)

    // Duplicate node with new children as children
    tryDuplicate(newNode, newChildren)
  }

  def executeBottomUp(node: A): A = {

    // At first recurse into children and get the new children
    val newChildren: Seq[Any] = recurseChildren(node, executeBottomUp)

    // In case duplicator is defined. Duplicate method  TODO otherwise do duplication ourselves
    val duplicatedNode: A = tryDuplicate(node, newChildren)

    // Rewrite the node
    if(rule.isDefinedAt(duplicatedNode)) {
      rule(duplicatedNode)
    } else {
      duplicatedNode
    }
  }

  def executeInnermost(node: A): A = ???

  def executeOutermost(node: A): A = ???

}

/**
  * A strategy that provides a context during rewriting. The user can control what is in the context by providing a updateContext method
  * that will be called for every ancestor of the node
  *
  * @param rule A partial function that describes the rewriting. It takes the candidate node for rewriting and the context as argument and delivers a rewritten node
  * @tparam A Supertype of every node we want to rewrite
  * @tparam C Supertype of the context
  */
class StrategyC[A, C](val rule: PartialFunction[(A, Context[A, C]), A]) extends StrategyInterface[A] {
  protected var upContext: PartialFunction[(A, C), C] = PartialFunction.empty
  protected var defaultContxt: Option[C] = None

  //<editor-fold desc="Overrides for DSL">

  override def traverse(t: Traverse): StrategyC[A, C] = {
    super.traverse(t)
    this
  }

  override def customChildren(c: PartialFunction[A, Seq[A]]): StrategyC[A, C] = {
    super.customChildren(c)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyC[A, C] = {
    super.recurseFunc(r)
    this
  }

  override def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): StrategyC[A, C] = {
    super.defineDuplicator(d)
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
      case Traverse.TopDown => executeTopDown(node, new Context[A, C](Seq(), defaultContxt.get, cChildren))
      case Traverse.BottomUp => executeBottomUp(node, new Context[A, C](Seq(), defaultContxt.get, cChildren))
      case Traverse.Innermost => executeInnermost(node, None)
      case Traverse.Outermost => executeOutermost(node, None)
    }
  }

  def executeTopDown(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context(context.ancestors ++ Seq(node), context.custom, cChildren)

    // Check which node we get from rewriting
    val newNode: A = if (rule.isDefinedAt((node, newContext))) {
      rule((node, newContext))
    } else {
      node
    }

    // Create the new Context for children recursion
    newContext = new Context[A, C](newContext.ancestors, if (upContext.isDefinedAt(newNode, newContext.custom)) {
      upContext(newNode, context.custom)
    } else {
      newContext.custom
    }, cChildren)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    duplicator.applyOrElse((newNode, newChildren.asInstanceOf[Seq[Product]]), (x: Tuple2[A, Seq[Product]]) => newNode)
  }

  def executeBottomUp(node: A, context: Context[A,C]): A =  {
    // Add this node to context
    val newContext = new Context(context.ancestors ++ Seq(node), if (upContext.isDefinedAt(node, context.custom)) {
      upContext(node, context.custom)
    } else {
      context.custom
    }, cChildren)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(node, executeBottomUp(_, newContext))

    val newNode = duplicator.applyOrElse((node, newChildren.asInstanceOf[Seq[Product]]), (x: Tuple2[A, Seq[Product]]) => node)

    if (rule.isDefinedAt((newNode, newContext))) {
      rule((newNode, newContext))
    } else {
      newNode
    }
  }

  def executeInnermost(node: A, context: Option[C]): A = ???

  def executeOutermost(node: A, context: Option[C]): A = ???

}

class Context[A, C](val ancestors: Seq[A], val custom: C, private val childFunc: PartialFunction[A, Seq[A]]) {

  lazy val node = ancestors.last

  /**
    * The predecessor child of the parent that follows the node itself
    */
  lazy val previous: Option[Any] = predecessors.lastOption

  /**
    * All children of the parent of a node that precede the node itself
    */
  lazy val predecessors: Seq[Any] = {



    //val index: Int = family.indexWhere((x) => System.identityHashCode(x) == System.identityHashCode(node))
    val index: Int = family indexWhere ( isEqualNode )
    family.splitAt(index + 1)._1.dropRight(1)
  }

  /**
    * The successor child of the parent that follows the node itself
    */
  lazy val next: Option[Any] = successors.headOption

  /**
    * All children of the parent of a node that follow the node itself
    */
  lazy val successors: Seq[Any] = {
    //val index: Int = family.indexWhere((x) => System.identityHashCode(x) == System.identityHashCode(node))
    val index: Int = family indexWhere ( isEqualNode )
    family.splitAt(index + 1)._2
  }

  /**
    * All children of the parent without the node itself
    */
  lazy val siblings: Seq[Any] = family.drop(family.indexOf(node))

  /**
    * All children of the parent
    */
  lazy val family: Seq[Any] = {
    if (childFunc.isDefinedAt(parent)) {
      childFunc(parent)
    } else {
      node match {
        case p: Product => (0 until p.productArity) map { x: Int => p.productElement(x) }
        case rest =>
          println("We do not support nodes that don't implement product")
          Seq()
      }
    }
  }

  /**
    * Parent of node
    */
  lazy val parent: A = ancestors.dropRight(1).last

  def isEqualNode(elem:Any) = elem match { // TODO get consistent idea of a child
    case Some(x:AnyRef) => x eq node.asInstanceOf[AnyRef]
    case Seq(_) => false
    case p:AnyRef => p eq node.asInstanceOf[AnyRef]
  }

}


class Query[A, B](val getInfo: PartialFunction[A, B]) extends StrategyInterface[A] {

  protected var accumulator: Seq[B] => B = (x: Seq[B]) => x.head
  protected var nElement: Option[B] = None

  def getAccumulator = accumulator

  def accumulate(a: Seq[B] => B): Query[A, B] = {
    accumulator = a
    this
  }

  def getNeutralElement = nElement

  def neutralElement(ne: B): Query[A, B] = {
    nElement = Some(ne)
    this
  }

  override def traverse(t: Traverse): Query[A, B] = {
    super.traverse(t)
    this
  }

  override def customChildren(c: PartialFunction[A, Seq[A]]): Query[A, B] = {
    super.customChildren(c)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Query[A, B] = {
    super.recurseFunc(r)
    this
  }

  override def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): Query[A, B] = {
    print("A Query will not create nodes. Defining a duplicator is not neccessary")
    super.defineDuplicator(d)
    this
  }

  override def execute(node: A): B = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node)
      case Traverse.BottomUp => executeBottomUp(node)
      case Traverse.Innermost => executeInnermost(node)
      case Traverse.Outermost => executeOutermost(node)
    }
  }

  def executeTopDown(node: A): B = {
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
    val children: Seq[Any] = if (cChildren.isDefinedAt(node)) {
      cChildren(node)
    } else node match {
      case p: Product => ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
        case s: Seq[Product] => s
        case o: Option[Product] => o
        case i: Product => i.asInstanceOf[A]
      }
      case rest =>
        assert(false, "We do not support nodes that don't implement product")
        Seq()
    }


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
          case o: Option[Product] => o match {
            case None => None
            case Some(node: Product) => Some(executeTopDown(node.asInstanceOf[A]))
          }
          case s: Seq[Product] => Some(accumulator(s map { x => executeTopDown(x.asInstanceOf[A]) }))
          case n: Product => Some(executeTopDown(n.asInstanceOf[A]))
        }
      } else {
        None
      }
    }
    accumulator(Seq(qResult) ++ (seqResults collect { case Some(x: B) => x }))
  }

  def executeBottomUp(node: A): B = ???

  def executeInnermost(node: A): B = ???

  def executeOutermost(node: A): B = ???
}