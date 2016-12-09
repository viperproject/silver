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
  protected var duplicator: PartialFunction[(A, Seq[A]), A] = PartialFunction.empty

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

  def defineDuplicator(d: PartialFunction[(A, Seq[A]), A]): StrategyInterface[A] = {
    duplicator = d
    this
  }

  def executeTopDown(node: A): A

  def executeBottomUp(node: A): A

  def executeInnermost(node: A): A

  def executeOutermost(node: A): A

  def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node)
      case Traverse.BottomUp => executeBottomUp(node)
      case Traverse.Innermost => executeInnermost(node)
      case Traverse.Outermost => executeOutermost(node)
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

  override def defineDuplicator(d: PartialFunction[(A, Seq[A]), A]): Strategy[A] = {
    super.defineDuplicator(d)
    this
  }

  override def executeTopDown(node: A): A = {
    // TODO Replace printouts with actual exceptions

    // Check which node we get from rewriting
    val newNode = if (rule.isDefinedAt(node)) rule(node) else node

    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children: Seq[A] = if (cChildren.isDefinedAt(newNode)) {
      cChildren(newNode)
    } else {
      newNode match {
        case p: Product => ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
          case i: Product => i.asInstanceOf[A]
        }
        case rest =>
          println("We do not support nodes that dont implement product")
          Seq()
      }
    }

    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = if (recursionFunc.isDefinedAt(newNode)) {
      recursionFunc(newNode)
    } else {
      children.indices map { x => true }
    }
    // Check whether the list of indices is of correct length
    if (childrenSelect.length != children.length) print("Incorrect number of children in recursion")


    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[A] = children.zip(childrenSelect) map {
      case (child, b) => if (b) {
        child match {
          case n: Product => executeTopDown(n.asInstanceOf[A])
          case rest => rest
        }
      } else {
        child
      }
    }

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    if (duplicator.isDefinedAt(newNode, newChildren)) {
      duplicator(newNode, newChildren)
    } else {
      newNode
    }
  }

  override def executeBottomUp(node: A): A = ???

  override def executeInnermost(node: A): A = ???

  override def executeOutermost(node: A): A = ???
}

/*class StrategyC[A, C](val rule: PartialFunction[(A, Seq[C]), A]) extends StrategyInterface[A] {
  protected var updateContext: PartialFunction[A, C] = PartialFunction.empty

  def updateContext(p: PartialFunction[A, C]): StrategyC[A, C] = {
    updateContext = p
    this
  }

  override def traverse(t: Traverse): StrategyC[A, C] = {
    super.traverse(t)
    this
  }

  override def recurse(r: Recurse): StrategyC[A, C] = {
    super.recurse(r)
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

  override def executeTopDown(node: A): A = ???

  override def executeBottomUp(node: A): A = ???

  override def executeInnermost(node: A): A = ???

  override def executeOutermost(node: A): A = ???
}

class Query[A,B](val rule: PartialFunction[A, B]) extends StrategyInterface[A] {

  protected var accumulator: Seq[B] => B = (x:Seq[B]) => x.head

  def getAccumulator = accumulator
  def accumulate(a: Seq[B] => B):StrategyInterface[A] = {
    accumulator = a
    this
  }

  override def traverse(t: Traverse): Query[A,B] = {
    super.traverse(t)
    this
  }

  override def recurse(r: Recurse): Query[A,B] = {
    super.recurse(r)
    this
  }

  override def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Query[A,B] = {
    super.recurseFunc(r)
    this
  }

  override def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): Query[A,B] = {
    super.defineDuplicator(d)
    this
  }

  override def executeTopDown(node: A): A = ???

  override def executeBottomUp(node: A): A = ???

  override def executeInnermost(node: A): A = ???

  override def executeOutermost(node: A): A = ???
}*/