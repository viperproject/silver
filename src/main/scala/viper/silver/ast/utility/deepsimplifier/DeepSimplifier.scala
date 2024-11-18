package viper.silver.ast.utility.deepsimplifier

import viper.silver.ast._

import scala.collection.mutable
import scala.collection.mutable._

object DeepSimplifier {

  def simplify[N <: Node](n: N): N = {

    val visited: ArrayBuffer[N] = ArrayBuffer(n)
    val queue: mutable.Queue[N] = mutable.Queue(n)

    while (queue.nonEmpty) {
      val currnode: N = queue.dequeue()
      //val generated: ArrayBuffer[N] = recursiveSimplify(currnode)
      val generated: ArrayBuffer[N] = pfSimplify(currnode)

      for (g <- generated if !visited.contains(g)) {
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

  def pfSimplify[N <: Node](n: N): ArrayBuffer[N] = {

    val result: ArrayBuffer[Node] = ArrayBuffer()

    val cases: List[PartialFunction[N, Node]] = List(
      { case Not(Not(single)) => single },
      { case root@Or(TrueLit(), _) => TrueLit()(root.pos, root.info) },
      { case root@Or(_, TrueLit()) => TrueLit()(root.pos, root.info) }
    )

    result ++= cases.collect { case lcase if lcase.isDefinedAt(n) => lcase(n) }

    result.asInstanceOf[ArrayBuffer[N]]
  }

  def pfRecSimplify[N <: Node](n: N): ArrayBuffer[N] = {
    val result: ArrayBuffer[N] = ArrayBuffer()

    lazy val newChildrenList = n.children.zipWithIndex.flatMap { case (child: N, index) =>
      pfSimplify(child).map { pfSimpChild =>
        n.children.toList.updated(index, pfSimpChild)
      }
    }
    result ++= newChildrenList.map {
      newChildren => n.withChildren(newChildren)
    }
    result
  }



}
