package viper.silver.ast.utility

import viper.silver.ast.utility.Traverse.Traverse

/**
  * Created by simonfri on 05.12.2016.
  */


object Traverse extends Enumeration {
    type Traverse = Value
    val TopDown, BottomUp, Innermost, Outermost = Value
}

trait StrategyInterface[A] {

  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty
  protected var cChildren: PartialFunction[A, Seq[A]] = PartialFunction.empty
  protected var duplicator: PartialFunction[(A, Seq[A]), A] = PartialFunction.empty

  def getTraversionMode = traversionMode
  def traverse(t: Traverse):StrategyInterface[A] = {
    traversionMode = t
    this
  }

  def getcustomChildren = cChildren
  def customChildren(c: PartialFunction[A, Seq[A]]):StrategyInterface[A] = {
    cChildren = c
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]):StrategyInterface[A] = {
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


class Strategy[A](val rule: PartialFunction[A, A]) extends StrategyInterface[A] {

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
    val newNode = if (rule.isDefinedAt(node)) rule(node) else  node

    // Put all the children of this node into a sequence

    val children:Seq[A] = if (cChildren.isDefinedAt(newNode)) {
        cChildren(newNode)
      } else {
        newNode match {
          case p:Product => ((0 until p.productArity) map { x:Int => p.productElement(x) }) collect ({ case i: Product => i.asInstanceOf[A] })
          case rest => { println("We do not support nodes that dont implement product"); Seq() }
        }
      }

    // Get the indices of the sequence that we perform recursion on
    val childrenSelect = if(recursionFunc.isDefinedAt(newNode)) {
        recursionFunc(newNode)
    } else {
        children.indices map {x => true}
    }

    // Check whether the list of indices is of correct length
    if (childrenSelect.length != children.length) print("Incorrect number of children in recursion")


    // Recurse on children where bit is set TODO rewrite this I got problems with the type system there
    val func: (A,Boolean) => A = (x: A, b:Boolean) => {
      if(b) {
        x match {
          case n:Product =>  executeTopDown(n.asInstanceOf[A])
          case rest => rest
        }
      } else {
        x
      }
    }
    val newChildren:Seq[A] = children.zip(childrenSelect) map( x => func(x._1, x._2) )

    // Put the nodes together
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