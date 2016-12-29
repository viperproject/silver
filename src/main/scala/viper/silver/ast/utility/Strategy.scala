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

  def execute(node: A): Any

  /**
    * Following methods are helper methods for the other Strategy implementations
    */

  protected def recurseChildren(node: A, recurse:Function1[A, A]): Seq[Any] = {
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
  * @param rule A partial function that defines the rewriting.
  * @tparam A Supertype of every node we want to rewrite
  */
class Strategy[A <: Rewritable[A]](val rule: PartialFunction[A, A]) extends StrategyInterface[A] {

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
    val newNode = if (rule.isDefinedAt(node)) {
      rule(node)
    } else {
      node
    }

    // Then traverse children
    val newChildren: Seq[Any] = recurseChildren(newNode, executeTopDown)
    //println(newChildren map { x => x.getClass })
    // Duplicate node with new children as children
    newNode.duplicate(newChildren)
  }

  def executeBottomUp(node: A): A = {

    // At first recurse into children and get the new children
    val newChildren: Seq[Any] = recurseChildren(node, executeBottomUp)

    // In case duplicator is defined. Duplicate method  TODO otherwise do duplication ourselves
    val duplicatedNode: A = node.duplicate(newChildren)

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
class StrategyC[A <: Rewritable[A], C](val rule: PartialFunction[(A, Context[A, C]), A]) extends StrategyInterface[A] {
  protected var upContext: PartialFunction[(A, C), C] = PartialFunction.empty
  protected var defaultContxt: Option[C] = None

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
      case Traverse.Innermost => executeInnermost(node, None)
      case Traverse.Outermost => executeOutermost(node, None)
    }
  }

  def executeTopDown(node: A, context: Context[A, C]): A = {
    // Add this node to context
    var newContext = new Context(context.ancestors ++ Seq(node), context.custom)

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
    })

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(newNode, executeTopDown(_, newContext))

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    newNode.duplicate(newChildren)
  }

  def executeBottomUp(node: A, context: Context[A,C]): A =  {
    // Add this node to context
    val newContext = new Context(context.ancestors ++ Seq(node), if (upContext.isDefinedAt(node, context.custom)) {
      upContext(node, context.custom)
    } else {
      context.custom
    })

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren = recurseChildren(node, executeBottomUp(_, newContext))

    val newNode = node.duplicate(newChildren)

    if (rule.isDefinedAt((newNode, newContext))) {
      rule((newNode, newContext))
    } else {
      newNode
    }
  }

  def executeInnermost(node: A, context: Option[C]): A = ???

  def executeOutermost(node: A, context: Option[C]): A = ???

}

class Context[A <: Rewritable[A], C](val ancestors: Seq[A], val custom: C) {

  lazy val node = ancestors.last

  /**
    * The predecessor child of the parent that follows the node itself
    */
  lazy val previous: Option[Any] = predecessors.lastOption

  /**
    * All children of the parent of a node that precede the node itself
    */
  lazy val predecessors: Seq[Any] = family.takeWhile( !isEqualNode(_) )

  /**
    * The successor child of the parent that follows the node itself
    */
  lazy val next: Option[Any] = successors.headOption

  /**
    * All children of the parent of a node that follow the node itself
    */
  lazy val successors: Seq[Any] = family.dropWhile( !isEqualNode(_) ).drop(1)


  /**
    * All children of the parent without the node itself
    */
  lazy val siblings: Seq[Any] = family.filter( !isEqualNode(_))


  /**
    * All children of the parent. Sequence of nodes and options of nodes will be unfolded and the node itself is included in the list
    */
  lazy val family: Seq[Any] = parent.getChildren().foldLeft(Seq.empty[Any])( (children:Seq[Any],y:Any) =>  y match {
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
  lazy val parent: A = ancestors.dropRight(1).last

  def isEqualNode(elem:Any):Boolean = elem match { // TODO get consistent idea of a child
    case Some(x:AnyRef) => x eq node.asInstanceOf[AnyRef]
    case Seq(_) => false
    case p:AnyRef => p eq node.asInstanceOf[AnyRef]
  }

}


class Query[A <: Rewritable[A], B](val getInfo: PartialFunction[A, B]) extends StrategyInterface[A] {

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

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Query[A, B] = {
    super.recurseFunc(r)
    this
  }

  override def execute(node: A): B = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node)
      case Traverse.BottomUp => executeTopDown(node)
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
            case Some(node: Rewritable[A]) => Some(executeTopDown(node.asInstanceOf[A]))
          }
          case s: Seq[Rewritable[A]] => Some(accumulator(s map { x => executeTopDown(x.asInstanceOf[A]) }))
          case n: Rewritable[A] => Some(executeTopDown(n.asInstanceOf[A]))
        }
      } else {
        None
      }
    }
    accumulator(Seq(qResult) ++ (seqResults collect { case Some(x: B) => x }))
  }

  def executeInnermost(node: A): B = ???

  def executeOutermost(node: A): B = ???
}