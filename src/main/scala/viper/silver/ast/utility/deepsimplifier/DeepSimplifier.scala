package viper.silver.ast.utility.deepsimplifier

import viper.silver.ast._

import scala.collection.mutable
import scala.collection.mutable._

object DeepSimplifier {

  def simplify[N <: Node](n: N): N = {

    val visited: ArrayBuffer[N] = ArrayBuffer(n)
    val queue: mutable.Queue[N] = mutable.Queue(n)

    while (queue.nonEmpty && visited.length < 50000) { //TODO: hardcoded stop, make this an input
      val currnode: N = queue.dequeue()
      println("currnode: " + currnode)
      val generated: ArrayBuffer[N] = pfRecSimplify(currnode)
      println("generated: " + generated)

      for (g <- generated if !visited.contains(g)) {

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
      { case root@Not(BoolLit(literal)) => BoolLit(!literal)(root.pos, root.info) },
      { case root@Not(EqCmp(a, b)) => NeCmp(a, b)(root.pos, root.info) },
      { case root@Not(NeCmp(a, b)) => EqCmp(a, b)(root.pos, root.info) },
      { case root@Not(GtCmp(a, b)) => LeCmp(a, b)(root.pos, root.info) },
      { case root@Not(GeCmp(a, b)) => LtCmp(a, b)(root.pos, root.info) },
      { case root@Not(LtCmp(a, b)) => GeCmp(a, b)(root.pos, root.info) },
      { case root@Not(LeCmp(a, b)) => GtCmp(a, b)(root.pos, root.info) },

      //TODO
      { case root@NeCmp(left, right) => Not(EqCmp(left, right)())(root.pos, root.info)},

      { case Not(Not(single)) => single },

      { case Or(FalseLit(), right) => right },
      { case Or(left, FalseLit()) => left },
      { case root@Or(TrueLit(), _) => TrueLit()(root.pos, root.info) },
      { case root@Or(_, TrueLit()) => TrueLit()(root.pos, root.info) },

      { case And(TrueLit(), right) => right },
      { case And(left, TrueLit()) => left },
      { case root@And(FalseLit(), _) => FalseLit()(root.pos, root.info) },
      { case root@And(_, FalseLit()) => FalseLit()(root.pos, root.info) },

      //associativity
      //WARNING: position and info attribute not correctly maintained for lchild, left and right
      { case root@And(lchild@And(left, right), rchild) => And(left, And(right, rchild)())(root.pos, root.info)},
      { case root@And(lchild, rchild@And(left, right)) => And(And(lchild, left)(), right)(root.pos, root.info)},

      { case root@Or(lchild@Or(left, right), uright) => Or(left, Or(right, uright)())(root.pos, root.info)},
      { case root@Or(uleft, rchild@Or(left, right)) => Or(Or(uleft, left)(), right)(root.pos, root.info)},

      //implication rules

      { case root@Implies(FalseLit(), _) => TrueLit()(root.pos, root.info) },
      { case Implies(TrueLit(), consequent) => consequent },
      { case root@Implies(l1, Implies(l2, r)) => Implies(And(l1, l2)(), r)(root.pos, root.info) },

      { case And(Implies(l1, r1), Implies(Not(l2), r2)) if(l1 == l2 && r1 == r2) => r1 },

      //contrapositive
      { case root@Implies(left, right) => Implies(Not(right)(), Not(left)())(root.pos, root.info) },
      { case root@Implies(Not(left), Not(right)) => Implies(right, left)(root.pos, root.info) },

      //modus ponens & modus tollens

      //implies to or
      { case root@Implies(left, right) => Or(Not(left)(), right)(root.pos, root.info)},
      { case root@Or(Not(left), right) => Implies(left, right)(root.pos, root.info)},

      //extended rules and/or
      //pos attribute!!
      { case root@Not(nchild@And(left, right)) => And(Not(left)(), Not(right)())(root.pos, root.info)},
      { case root@And(Not(left), Not(right)) => Not(And(left, right)())(root.pos, root.info)},


      //de morgan
      { case root@Not(Or(left, right)) => And(Not(left)(), Not(right)())(root.pos, root.info)},
      { case root@And(Not(left), Not(right)) => Not(Or(left, right)())(root.pos, root.info)},

      { case root@Not(And(left, right)) => Or(Not(left)(), Not(right)())(root.pos, root.info)},
      { case root@Or(Not(left), Not(right)) => Not(And(left, right)())(root.pos, root.info)},







    )

    result ++= cases.collect { case lcase if lcase.isDefinedAt(n) => lcase(n) }

    result.asInstanceOf[ArrayBuffer[N]]
  }

  def pfRecSimplify[N <: Node](n: N): ArrayBuffer[N] = {
    val result: ArrayBuffer[N] = ArrayBuffer()
    result ++= pfSimplify(n)
    val newChildrenList = n.children.zipWithIndex.map {
      case (child: AtomicType, index) => {
        ArrayBuffer()
      }
      case (child: N, index) => {
        val temp = new ArrayBuffer[List[Any]]()
          temp ++=pfSimplify(child).map { pfSimpChild =>
          n.children.toList.updated(index, pfSimpChild)
        }
        temp ++= pfRecSimplify(child).toList.map { recSimpChild =>
          n.children.toList.updated(index, recSimpChild)
        }
        temp
      }
      case _ => {
        ArrayBuffer()
      }
    }

    var newlist = newChildrenList.map {
      newChildren => newChildren.map{
        oneChildren => {
          n.withChildren(oneChildren) }//withChildren has big performance impact!
      }
    }
    newlist.map (listelem => result ++= listelem)
    result
  }
}
