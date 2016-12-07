package viper.silver.ast.utility

import viper.silver.ast.utility.Recurse.Recurse
import viper.silver.ast.utility.Traverse.Traverse

/**
  * Created by simonfri on 05.12.2016.
  */


object Traverse extends Enumeration {
    type Traverse = Value
    val TopDown, BottomUp, Innermost, Outermost = Value
}

object Recurse extends Enumeration {
  type Recurse = Value
  val One, Some, All, None = Value
}

trait StrategyInterface[A] {

  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionMode: Recurse = Recurse.None
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty
  protected var duplicator: PartialFunction[(A, Seq[Any]), A] = PartialFunction.empty

  def getTraversionMode = traversionMode
  def traverse(t: Traverse):StrategyInterface[A] = {
    traversionMode = t
    this
  }

  def getRecursionMode = recursionMode
  def recurse(r: Recurse):StrategyInterface[A] = {
    recursionMode = r
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]):StrategyInterface[A] = {
    recursionFunc = r
    this
  }

  def defineDuplicator(d: PartialFunction[(A, Seq[Any]), A]): StrategyInterface[A] = {
    duplicator = d
    this
  }

  def execute(node: A): A
}


class Strategy[A](val rule: PartialFunction[A, A]) extends StrategyInterface[A] {

  override def execute(node: A): A = ???

  override def traverse(t: Traverse): Strategy[A] = {
    super.traverse(t)
    this
  }

  override def recurse(r: Recurse): Strategy[A] = {
    super.recurse(r)
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

}

class StrategyC[A, C](val rule: PartialFunction[(A, Seq[C]), A]) extends StrategyInterface[A] {
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

  override def execute(node: A): A = ???



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

  override def execute(node: A): B = ???


}