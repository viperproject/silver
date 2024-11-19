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
      println("currnode: " + currnode)
      //val generated: ArrayBuffer[N] = recursiveSimplify(currnode)
      val generated: ArrayBuffer[N] = pfRecSimplify(currnode)
      println("generated: " + generated)

      for (g <- generated if !visited.contains(g)) {
        //println("new g: " + g)

        visited.append(g)
        queue.enqueue(g)
      }
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


    val newChildrenList = n.children.zipWithIndex.map {
      case (child: AtomicType, index) => {
        //println(child)
        //println("case1: " + ArrayBuffer(n.children.toList))
        Nil
        ArrayBuffer(n.children.toList)
      }
      case (child: N, index) => {
        //println("case2")
        val temp = new ArrayBuffer[List[Any]]()
          temp ++=pfSimplify(child).map { pfSimpChild =>
          n.children.toList.updated(index, pfSimpChild)
        }
        //println("case2: " + temp)
        temp ++= pfRecSimplify(child).toList.map { recSimpChild =>
          n.children.toList.updated(index, recSimpChild)
        }
        //println("case2after: " + temp)
        temp
      }
      case _ => {
        //println("case3: " + ArrayBuffer(n.children.toList))
        ArrayBuffer(n.children.toList)
      }
    }
    //println(n.children)
    //println(newChildrenList)
    var newlist = newChildrenList.map {
      newChildren => newChildren.map{
        oneChildren => {
          //println(n.children)
          //println(oneChildren)
          n.withChildren(oneChildren) }//big performance impact! using withChildren
      }
    }
    newlist.map (listelem => result ++= listelem)
    //println("result: " + result)
    result
  }
}
