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
  protected var creationFunc: PartialFunction[(A,A), A] = PartialFunction.empty

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

  def recurse(r: PartialFunction[A, Seq[Boolean]]):StrategyInterface[A] = {
    recursionFunc = r
    this
  }

  def perserveData(p: PartialFunction[(A,A), A]): StrategyInterface[A] = {
    creationFunc = p
    this
  }

  def execute(node: A): A
}


class Strategy[A](val rule: PartialFunction[A, A]) extends StrategyInterface[A] {

  override def execute(node: A): A = ???

}

class StrategyC[A](val rule: PartialFunction[(A, Seq[A]), A]) extends StrategyInterface[A] {

  override def execute(node: A): A = ???


}

class Query[A,B](val rule: PartialFunction[A, B]) extends StrategyInterface[A] {

  protected var accumulator: Seq[B] => B = (x:Seq[B]) => x.head

  def getAccumulator = accumulator
  def accumulate(a: Seq[B] => B):StrategyInterface[A] = {
    accumulator = a
    this
  }

  override def execute(node: A): B = ???


}