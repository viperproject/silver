package viper.silver.ast.utility.deepsimplifier

import viper.silver.ast._

import scala.collection.mutable
import scala.collection.mutable._

object DeepSimplifier {

  def simplify[N <: Node](n: N, assumeWelldefinedness: Boolean = false, iterationLimit: Integer = 5000, printToConsole: Boolean = false): N = {

    val visited: ArrayBuffer[N] = ArrayBuffer(n)
    val queue: mutable.Queue[N] = mutable.Queue(n)

    while (queue.nonEmpty && visited.length < iterationLimit) {
      val currnode: N = queue.dequeue()
      if(printToConsole) {
        println("currnode: " + currnode)
      }

      val generated: ArrayBuffer[N] = pfRecSimplify(currnode, assumeWelldefinedness)
      if(printToConsole) {
        println("generated: " + generated)
      }
      for (g <- generated if !visited.contains(g)) {
        visited.append(g)
        queue.enqueue(g)
      }
    }

    if(printToConsole){
      println("result simplify: " + visited)
    }

    getShortest(visited)
  }

  // only called with nonempty ArrayBuffers TODO: what happens if empty?


  private def getShortest[N <: Node](visited: ArrayBuffer[N]): N = {
    visited.minBy(treeSize)
  }

  // "counts every node twice", ie "LocalVar("a", Bool)()" is counted once as "a" and once as "Bool", at least it's consistent

  private def treeSize[N <: Node](n: N): Int = {
    n.reduceTree[Int]((node, count) => (count.sum + 1))
  }
  private def treeHasDoubleNeg[N <: Node](n: N): Boolean = {
    n.reduceTree[Boolean]((node, doubleNegs) => doubleNegs.contains(true) || isDoubleNeg(node))
  }

  private def pfSimplify[N <: Node](n: N, assumeWelldefinedness: Boolean): ArrayBuffer[N] = {

    val result: ArrayBuffer[Node] = ArrayBuffer()

    val cases: List[PartialFunction[N, Node]] = List(
      { case root@Not(BoolLit(literal)) => BoolLit(!literal)(root.pos, root.info) },

      { case root@Not(EqCmp(a, b)) => NeCmp(a, b)(root.pos, root.info) },
      { case root@Not(NeCmp(a, b)) => EqCmp(a, b)(root.pos, root.info) },
      { case root@Not(GtCmp(a, b)) => LeCmp(a, b)(root.pos, root.info) },
      { case root@Not(GeCmp(a, b)) => LtCmp(a, b)(root.pos, root.info) },
      { case root@Not(LtCmp(a, b)) => GeCmp(a, b)(root.pos, root.info) },
      { case root@Not(LeCmp(a, b)) => GtCmp(a, b)(root.pos, root.info) },


      //TODO: try to find case where these could be used, then figure out a better way to implement them
      /*
      { case root@NeCmp(left, right) => Not(EqCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@EqCmp(left, right) => Not(NeCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@GtCmp(left, right) => Not(LeCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@GeCmp(left, right) => Not(LtCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@LtCmp(left, right) => Not(GeCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@LeCmp(left, right) => Not(GtCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      */

      { case Not(Not(single)) => single },

      { case Or(FalseLit(), right) => right },
      { case Or(left, FalseLit()) => left },
      { case root@Or(TrueLit(), _) => TrueLit()(root.pos, root.info) },
      { case root@Or(_, TrueLit()) => TrueLit()(root.pos, root.info) },

      { case And(TrueLit(), right) => right },
      { case And(left, TrueLit()) => left },
      { case root@And(FalseLit(), _) => FalseLit()(root.pos, root.info) },
      { case root@And(_, FalseLit()) => FalseLit()(root.pos, root.info) },

      //Idempotence
      { case root@And(a, b) if assumeWelldefinedness && a == b => a},
      { case root@Or(a, b) if assumeWelldefinedness && a == b => a},

      { case root@And(a, b) => And(b, a)(root.pos, root.info)},
      { case root@Or(a, b) => Or(b, a)(root.pos, root.info)},


      //associativity
      //WARNING: position and info attribute not correctly maintained for lchild, left and right
      { case root@And(lchild@And(left, right), rchild) => And(left, And(right, rchild)())(root.pos, root.info)},
      { case root@And(lchild, rchild@And(left, right)) => And(And(lchild, left)(), right)(root.pos, root.info)},

      { case root@Or(lchild@Or(left, right), uright) => Or(left, Or(right, uright)())(root.pos, root.info)},
      { case root@Or(uleft, rchild@Or(left, right)) => Or(Or(uleft, left)(), right)(root.pos, root.info)},

      //implication rules
      //WARNING: position and info attributes not correctly maintained
      { case root@Implies(FalseLit(), _) => TrueLit()(root.pos, root.info) },
      { case Implies(TrueLit(), consequent) => consequent },
      { case root@Implies(l1, Implies(l2, r)) => Implies(And(l1, l2)(), r)(root.pos, root.info) },

      { case And(Implies(l1, r1), Implies(Not(l2), r2)) if assumeWelldefinedness && (l1 == l2 && r1 == r2) => r1 },

      { case root@And(Implies(a, b), Implies(a2, c)) if a == a2 => Implies(a, And(b, c)())(root.pos, root.info) },
      { case And(Implies(a, b), Implies(Not(a2), b2)) if assumeWelldefinedness && a == a2 && b == b2 => b },
      { case root@And(a, Implies(a2, b)) if a == a2 => And(a, b)(root.pos, root.info) },

      //contrapositive
      //{ case root@Implies(left, right) if !(isDoubleNeg(left) || isDoubleNeg(right)) => Implies(Not(right)(), Not(left)())(root.pos, root.info) },
      { case root@Implies(Not(left), Not(right)) => Implies(right, left)(root.pos, root.info) },

      //modus ponens & modus tollens

      //implies to or
      //{ case root@Implies(left, right) if !(isDoubleNeg(left) || isDoubleNeg(left)) => Or(Not(left)(), right)(root.pos, root.info)},
      //{ case root@Or(Not(left), right) if !(isDoubleNeg(left) || isDoubleNeg(left)) => Implies(left, right)(root.pos, root.info)},

      //extended rules and/or
      //pos attribute!!

      //de morgan
      { case root@Not(Or(left, right)) => And(Not(left)(), Not(right)())(root.pos, root.info)},
      { case root@And(Not(left), Not(right)) => Not(Or(left, right)())(root.pos, root.info)},

      { case root@Not(And(left, right)) => Or(Not(left)(), Not(right)())(root.pos, root.info)},
      { case root@Or(Not(left), Not(right)) => Not(And(left, right)())(root.pos, root.info)},

      //equality comparison

      { case root@EqCmp(left, right) if assumeWelldefinedness && left == right => TrueLit()(root.pos, root.info) },
      { case root@EqCmp(BoolLit(left), BoolLit(right)) => BoolLit(left == right)(root.pos, root.info) },
      { case root@EqCmp(FalseLit(), right) => Not(right)(root.pos, root.info) },
      { case root@EqCmp(left, FalseLit()) => Not(left)(root.pos, root.info) },
      { case EqCmp(TrueLit(), right) => right },
      { case EqCmp(left, TrueLit()) => left },
      { case root@EqCmp(IntLit(left), IntLit(right)) => BoolLit(left == right)(root.pos, root.info) },
      { case root@EqCmp(NullLit(), NullLit()) => TrueLit()(root.pos, root.info) },

      //nonequality comparison

      { case root@NeCmp(BoolLit(left), BoolLit(right)) => BoolLit(left != right)(root.pos, root.info) },
      { case NeCmp(FalseLit(), right) => right },
      { case NeCmp(left, FalseLit()) => left },
      { case root@NeCmp(TrueLit(), right) => Not(right)(root.pos, root.info) },
      { case root@NeCmp(left, TrueLit()) => Not(left)(root.pos, root.info) },
      { case root@NeCmp(IntLit(left), IntLit(right)) => BoolLit(left != right)(root.pos, root.info) },
      { case root@NeCmp(NullLit(), NullLit()) => FalseLit()(root.pos, root.info) },
      { case root@NeCmp(left, right) if assumeWelldefinedness && left == right => FalseLit()(root.pos, root.info) },

      //extended equality/nonequality comparison
      //some possible rules could introduce more statements, but not these ones
      { case root@EqCmp(left, right) => EqCmp(right, left)(root.pos, root.info) },
      { case root@NeCmp(left, right) => NeCmp(right, left)(root.pos, root.info) },
      //{ case root@EqCmp(left, right) => Not(NeCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      //{ case root@NeCmp(left, right) => Not(EqCmp(left, right)(root.pos, root.info))(root.pos, root.info) },
      { case root@Not(EqCmp(left, right)) => NeCmp(left, right)(root.pos, root.info) },
      { case root@Not(NeCmp(left, right)) => EqCmp(left, right)(root.pos, root.info) },
      { case root@And(EqCmp(le, re), NeCmp(ln, rn)) if assumeWelldefinedness && le == ln && re == rn => FalseLit()(root.pos, root.info)},
      { case root@Or(EqCmp(le, re), NeCmp(ln, rn)) if assumeWelldefinedness && le == ln && re == rn => TrueLit()(root.pos, root.info)},

      //conditional expressions

      { case CondExp(TrueLit(), ifTrue, _) => ifTrue },
      { case CondExp(FalseLit(), _, ifFalse) => ifFalse },
      { case CondExp(_, ifTrue, ifFalse) if assumeWelldefinedness && ifTrue == ifFalse => ifTrue },
      { case root@CondExp(condition, FalseLit(), TrueLit()) => Not(condition)(root.pos, root.info) },
      { case CondExp(condition, TrueLit(), FalseLit()) => condition },
      { case root@CondExp(condition, FalseLit(), ifFalse) => And(Not(condition)(), ifFalse)(root.pos, root.info) },
      { case root@CondExp(condition, TrueLit(), ifFalse) =>
        if (ifFalse.isPure) {
          Or(condition, ifFalse)(root.pos, root.info)
        } else {
          Implies(Not(condition)(), ifFalse)(root.pos, root.info)
        }
      },
      { case root@CondExp(condition, ifTrue, FalseLit()) => And(condition, ifTrue)(root.pos, root.info) },
      { case root@CondExp(condition, ifTrue, TrueLit()) => Implies(condition, ifTrue)(root.pos, root.info) },

      //forall&exists

      //extended rules equality comparison

      //accessibility

      //fieldaccess and/extends locationaccess (see Expression.scala)
      //locationaccess: loc
      //fieldaccess: field and loc
      //example: fieldaccess(loc.next) && locationaccess(loc) => locationaccess(loc)
      //fieldaccess: layers? maybe go from field -> field.parent? or is field guaranteed to be a direct child?
    )

    result ++= cases.collect { case lcase if lcase.isDefinedAt(n) => lcase(n) }

    result.asInstanceOf[ArrayBuffer[N]]
  }

  private def isSingleNeg[N <: Node](n: N): Boolean = n match {
    case Not(_) => true
    case _ => false
  }

  private def isDoubleNeg[N <: Node](n: N): Boolean = n match {
    case Not(Not(_)) => true
    case _ => false
  }

  private def pfRecSimplify[N <: Node](n: N, assumeWelldefinedness: Boolean): ArrayBuffer[N] = {
    val result: ArrayBuffer[N] = ArrayBuffer()
    result ++= pfSimplify(n, assumeWelldefinedness)
    val newChildrenList = n.children.zipWithIndex.map {
      case (child: AtomicType, index) => {
        ArrayBuffer()
      }
      case (child: N, index) => {
        val temp = new ArrayBuffer[List[Any]]()
          temp ++=pfSimplify(child, assumeWelldefinedness).map { pfSimpChild =>
          n.children.toList.updated(index, pfSimpChild)
        }
        temp ++= pfRecSimplify(child, assumeWelldefinedness).toList.map { recSimpChild =>
          n.children.toList.updated(index, recSimpChild)
        }
        temp
      }
      case _ => {
        ArrayBuffer()
      }
    }

    val newlist = newChildrenList.map {
      newChildren => newChildren.map{
        oneChildren => {
          n.withChildren(oneChildren) }//withChildren has big performance impact!
      }
    }
    newlist.map (listelem => result ++= listelem)
    result
  }
}
