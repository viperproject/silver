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

  def execute(node: A): A
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
    val newNode = rule.applyOrElse(rule(node), identity[A])

    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children: Seq[Any] = cChildren.applyOrElse(newNode, (node: A) => node match {
      case p: Product => ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
        case s: Seq[Product] => s
        case o: Option[Product] => o
        case i: Product => i.asInstanceOf[A]
      }
      case rest =>
        assert(false, "We do not support nodes that don't implement product")
        Seq()
    })


    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = recursionFunc.applyOrElse(newNode, (node:A) => {
      children.indices map { x => true }
    })
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length != children.length, "Incorrect number of children in recursion")


    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[Any] = children.zip(childrenSelect) map {
      case (child, b) => if (b) {
        child match {
          case o: Option[Product] => {
            case None => None
            case Some(node) => Some(executeTopDown(node.asInstanceOf[A]))
          }
          case s: Seq[Product] => s map { x => executeTopDown(x.asInstanceOf[A]) }
          case n: Product => executeTopDown(n.asInstanceOf[A])
          case rest => rest
        }
      } else {
        child
      }
    }

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    duplicator.applyOrElse((newNode, newChildren), (x:Tuple2[A, Seq[A]]) => x._1)
  }

  def executeBottomUp(node: A): A = ???

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
class StrategyC[A, C](val rule: PartialFunction[(A, Option[C]), A]) extends StrategyInterface[A] {
  protected var upContext: PartialFunction[(A, Option[C]), Option[C]] = PartialFunction.empty

  //<editor-fold desc="Overrides for DSL">

  override def traverse(t: Traverse): StrategyC[A, C] = {
    super.traverse(t)
    this
  }

  override def customChildren(c: PartialFunction[A, Seq[A]]): StrategyInterface[A] = {
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

  def updateContext(p: PartialFunction[(A, Option[C]), Option[C]]): StrategyC[A, C] = {
    upContext = p
    this
  }

  override def execute(node: A): A = {
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node, None)
      case Traverse.BottomUp => executeBottomUp(node, None)
      case Traverse.Innermost => executeInnermost(node, None)
      case Traverse.Outermost => executeOutermost(node, None)
    }
  }

  def executeTopDown(node: A, context: Option[C]): A = {

    // Check which node we get from rewriting
    val newNode: A = rule.applyOrElse((node, context), (x:Tuple2[A, Option[C]]) => node)

    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children: Seq[Any] = cChildren.applyOrElse(newNode, (x:A) => x match {
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
    val childrenSelect = recursionFunc.applyOrElse(newNode, (node:A) => {
      children.indices map { x => true }
    })
    // Check whether the list of indices is of correct length
    //if (childrenSelect.length != children.length) print("Incorrect number of children in recursion")

    // Create the new Context for children recursion
    val newContext: Option[C] = if (upContext.isDefinedAt(newNode, context)) {
      upContext(newNode, context)
    } else {
      context
    }

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[Any] = children.zip(childrenSelect) map {
      case (child, b) => if (b) {
        child match {
          case o: Option[Product] => {
            case None => None
            case Some(node) => Some(executeTopDown(node.asInstanceOf[A], newContext))
          }
          case s: Seq[Product] => s map { x => executeTopDown(x.asInstanceOf[A], newContext) }
          case n: Product => executeTopDown(n.asInstanceOf[A], newContext)
          case rest => rest
        }
      } else {
        child
      }
    }

    // Create the new node by providing the rewritten node and the newChildren to a user provided Duplicator function,
    // that creates a new immutable node
    duplicator.applyOrElse((newNode, newChildren), (x:Tuple2[A, Seq[Any]]) => newNode)
  }

  def executeBottomUp(node: A, context: Option[C]): A = ???

  def executeInnermost(node: A, context: Option[C]): A = ???

  def executeOutermost(node: A, context: Option[C]): A = ???
}

/*
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