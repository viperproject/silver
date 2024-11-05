package viper.silver.ast.utility.deepsimplifier

import viper.silver.ast._
import viper.silver.ast.utility.rewriter.StrategyBuilder

import scala.collection.mutable
import scala.collection.mutable._

object DeepSimplifier {

  def simplify[N <: Node](n: N): N = {

    val visited: ArrayBuffer[N] = ArrayBuffer(n)
    val queue: mutable.Queue[N] = mutable.Queue(n)

    while(queue.nonEmpty){
      val currnode: N = queue.dequeue()
      //val generated: ArrayBuffer[N] = recursiveSimplify(currnode)
      val generated: ArrayBuffer[N] = pfSimplify(currnode).asInstanceOf[ArrayBuffer[N]]

      for(g <- generated if !visited.contains(g)) {
        //println("new g: " + g)
        visited.append(g)
        queue.enqueue(g)
      }
      queue.enqueueAll(generated)
    }

    println("result simplify: " + visited)

    getShortest(visited)
  }

  // only called with nonempty ArrayBuffers TODO: what happens if empty?
  // TODO: make private

  def getShortest[N <: Node](visited: ArrayBuffer[N]): N = {
    visited.minBy(treeSize)
  }

  // "counts every node twice", ie "LocalVar("a", Bool)()" is counted once as "a" and once as "Bool", at least it's consistent
  // TODO: make private
  def treeSize[N <: Node](n: N): Int = {
    n.reduceTree[Int]((node, count) => (count.sum + 1))
  }

  def pfSimplify[N <: Node](n: N): ArrayBuffer[Node] = {

    val result: ArrayBuffer[Node] = ArrayBuffer()

    val cases: List[PartialFunction[Node, Node]] = List(
      { case Not(Not(single)) => single},
      { case root@Or(TrueLit(), _) => TrueLit()(root.pos, root.info)},
      { case root@Or(_, TrueLit()) => TrueLit()(root.pos, root.info)}
    )

    result ++= cases.collect{ case lcase if lcase.isDefinedAt(n) => lcase(n)}

    result
  }

  //TODO: make private
  //TODO: does not necessarily need to know what type n itself is?
  // just be able to apply simpOneNode to a child and return the simplified version with the same child
  // use nodes? BinExp?
  //TODO: why fallthrough?

  def recursiveSimplify[N <: Node](n: N): ArrayBuffer[N] = {

    val result: ArrayBuffer[N] = ArrayBuffer()
    val versions: ArrayBuffer[N] = ArrayBuffer()

    result ++= simpOneNode(n)

    /*n.children.map {child =>
      val simps = simpOneNode(child).map {
        simp => n.replace (case child => simp)
      }
    }

    n.*/
    
    n match {
      case LocalVar => (result) ++= versions

      case Not(a) =>
        val childrenS: ArrayBuffer[N] = recursiveSimplify(a.asInstanceOf[N])
        for (c <- childrenS) {
          result += Not(c.asInstanceOf[Exp])().asInstanceOf[N]
        }

        (result) ++= simpOneNode(n)

      case And(a, b) =>
        val aS: ArrayBuffer[N] = recursiveSimplify(a.asInstanceOf[N])
        val bS: ArrayBuffer[N] = recursiveSimplify(b.asInstanceOf[N])

        for (saS <- aS) {
          for (sbS <- bS) {
            result += And(saS.asInstanceOf[Exp], sbS.asInstanceOf[Exp])().asInstanceOf[N]
          }
        }
      case _ =>
    }
    (result)
  }

  //TODO: make private, remove test4 from DeepSimplifierTest
  //TODO: figure out how to add result without casting to N (asInstanceOf[N])
  //TODO: better pattern matching (?)

  def simpOneNode[N <: Node](n: Node): ArrayBuffer[N] = {

    val result: ArrayBuffer[N] = ArrayBuffer()

    if(n.isInstanceOf[Not] && n.asInstanceOf[Not].exp.isInstanceOf[Not]) {
      result += n.asInstanceOf[Not].exp.asInstanceOf[Not].exp.asInstanceOf[N]
    }
    if(n.isInstanceOf[And] && n.asInstanceOf[And].left.isInstanceOf[TrueLit]) {
      result += n.asInstanceOf[And].right.asInstanceOf[N]
    }
    if(n.isInstanceOf[And] && n.asInstanceOf[And].right.isInstanceOf[TrueLit]) {
      result += n.asInstanceOf[And].left.asInstanceOf[N]
    }

    result
  }

  /*def contains(n: Node): Boolean = {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()

    val c = Or(a, b)()

    val visited: List[Node] = List(c)

    visited.contains(n)
  }*/
}
