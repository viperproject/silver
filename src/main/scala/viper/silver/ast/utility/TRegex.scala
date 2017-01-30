package viper.silver.ast.utility

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._
import viper.silver.ast.utility.Nesting.Nesting

import scala.language.implicitConversions

class ChildMatch[+N]() {

}

case class cN[N]() extends ChildMatch[N] {}

object ** extends ChildMatch

object ? extends ChildMatch

object Nesting extends Enumeration {
  type Nesting = Value
  val Start, Deep, Direct = Value
}

case class Quantity(q: Int = 1) {}
object PLUS extends Quantity(-2)
object STAR extends Quantity(-1)

object Quantity {
  def star = Quantity(-1)

  def plus = Quantity(-2)
}

class RegexStrategy[N <: Rewritable, C](private val matchSeq: Seq[(Nesting, Match)], private val p: PartialFunction[(N, ContextC[N, Seq[C]]), N]) extends StrategyInterface[N] {

  def goFurther(node: N, m: Match): Boolean = m match {
    case nodeMatch: n => nodeMatch.valid(node)
    case rewriteMatch: r => rewriteMatch.valid(node)
    case nodePredicate: nP[N] => nodePredicate.valid(node)
    case contextMatch: c[N] => contextMatch.valid(node).isDefined
    case goIntoChild: intoChild[N] => goIntoChild.valid(node).isDefined
    case _ => true
  }

  val allMatches = collection.mutable.HashSet.empty[nodeWithContext]

  // This hash set holds node context pairs that we will use to replace every matched node


  class nodeWithContext(val node: N, val context: Seq[C]) {
    /*override def equals(o: Any) = o match {
      case that: nodeWithContext => that.node eq node
      case _ => false
    }*/
  }

  type RegexContext = (Seq[(Nesting, Match)], Seq[C], Seq[nodeWithContext])

  override def execute[T <: N](startNode: N): T = {
    val findStarts = StrategyBuilder.ContextVisitor[N, RegexContext]({
      case (node, context) =>
        if (goFurther(node, context.custom._1.head._2)) {
          checkPath(node)
        }
    }, (matchSeq, Seq.empty[C], Seq.empty[nodeWithContext]))

    findStarts.visit(startNode)

    //HashSet is now filled with nodes to replace. Go do it!!
    val replaceStrat = StrategyBuilder.AncestorStrategy[N]({
      case (n, c) =>
        val nodeOption = allMatches.find(_.node eq n)
        if (nodeOption.isDefined) {
          val node2Replace = nodeOption.get
          val context = new ContextC[N, Seq[C]](c.ancestorList, node2Replace.context, c.transformer, PartialFunction.empty)
          if (p.isDefinedAt((n, context))) {
            p((n, context))
          } else {
            n
          }
        } else {
          n
        }
    })

    val result = replaceStrat.execute[T](startNode)
    result
  }

  // Check if a concrete path is a valid match
  def checkPath(StartNode: N): Unit = {
    // First element represents the matches, second is for having the context present in case of a rewrite match


    val nodesToUpdate = collection.mutable.HashSet.empty[nodeWithContext]

    // The update function specifies if we can consume a match and go further or if we continue with the current match
    val updateFunc: PartialFunction[(N, RegexContext), RegexContext] = {
      case (node, (matches, context, nodes)) =>
        if (matches.isEmpty) {
          // If matches is empty we have nothing to do. Just return and go on
          (matches, context, nodes)
        } else {
          val result = {
            val nextMatch = matches.head
            var newContext = context
            var newNodes = nodes

            // Context update done here, execute possible other actions that have to be performed in updateFunc here too
            nextMatch._2 match {
              case contextMatch: c[N] =>
                // Context update in case it is defined here
                val candContext = contextMatch.valid(node)
                if (candContext.isDefined) {
                  assert(candContext.isInstanceOf[C], "Context match from regex did not return the correct type")
                  newContext = newContext ++ Seq(candContext.asInstanceOf[C])
                }
              case rewriteMatch: r =>
                if (rewriteMatch.valid(node)) {
                  newNodes = newNodes ++ Seq(new nodeWithContext(node, newContext))
                }
              case _ =>
            }

            // Decide what happens next
            nextMatch._1 match {
              case Nesting.Direct | Nesting.Start =>
                if (goFurther(node, nextMatch._2)) {
                  // Find out if we match on the current node or not
                  // Match succeeded. Consume it and recurse with following matches
                  val newMatch = nextMatch._2.reduceQuantity()
                  if (newMatch.isDefined) (Seq((nextMatch._1, newMatch.get)) ++ matches.drop(1), newContext, newNodes) else (matches.drop(1), newContext, newNodes)
                } else {
                  // Return empty sequence because match failed. Nothing will change in further  recursion
                  (Seq.empty[(Nesting, Match)], context, newNodes)
                }
              case Nesting.Deep =>
                if (goFurther(node, nextMatch._2)) {
                  // Match succeeded. Consume it and recurse with following matches
                  (matches.drop(1), newContext, newNodes)
                } else {
                  // Match did not succeed. Maybe it will later
                  (matches, newContext, newNodes)
                }
            }
          }
          if (result._1.isEmpty) {
            // We now have an empty match but did not have one before.
            // This means that this path matches the whole regex and all nodes marked as rewritable on this path can be added to the rewriter
            result._3.foreach(nodesToUpdate.add)
          }
          result
        }

    }

    // This function performs actions of the according matches
    val actionFunc: (N, ContextC[N, RegexContext]) => Unit = (curNode, context) => {
      if (context.custom._1.nonEmpty) {
        val nextMatch = context.custom._1.head._2
        val ctxt = context.custom._2

        nextMatch match {
          case enterChild: intoChild[N] =>
            val childA = enterChild.valid(curNode)
            if (childA.isDefined) {
              assert(childA.get.isInstanceOf[N], "Child from intoChild does not extend node")
              val child = childA.get.asInstanceOf[Rewritable]
              curNode.getChildren foreach { n => if (child ne n.asInstanceOf[Rewritable]) context.transformer.noRec[N](child) }
            }
          case _ =>
        }
      }
    }

    val getMatchesStrat = StrategyBuilder.ContextVisitor[N, RegexContext](actionFunc, (matchSeq, Seq.empty[C], Seq.empty[nodeWithContext]), updateFunc)
    getMatchesStrat.visit(StartNode)

    nodesToUpdate.map( allMatches.add )

  }

}

class TRegex[N <: Rewritable, C](private val matchers: Seq[(Nesting, Match)] = Seq.empty[(Nesting, Match)]) {

  def |->(p: PartialFunction[(N, ContextC[N, Seq[C]]), N]): RegexStrategy[N, C] = {
    new RegexStrategy[N, C](matchers, p)
  }

  def %(m: Match): TRegex[N, C] = {
    if (matchers.isEmpty) {
      new TRegex(matchers ++ Seq((Nesting.Start, m)))
    }
    else {
      println("Only use % for starting a regex")
      this
    }
  }

  def >>(m: Match): TRegex[N, C] = {
    new TRegex(matchers ++ Seq((Nesting.Deep, m)))
  }

  def >(m: Match): TRegex[N, C] = {
    new TRegex(matchers ++ Seq((Nesting.Direct, m)))
  }


}

class SlimRegex[N <: Rewritable](private val matchers: Seq[(Nesting, Match)] = Seq.empty[(Nesting, Match)]) {

  def |->(p: PartialFunction[N, N]): Strategy[N, SimpleContext[N]] = {
    StrategyBuilder.SlimStrategy[N](p)
  }

  def %(m: Match): SlimRegex[N] = {
    if (matchers.isEmpty) {
      new SlimRegex(matchers ++ Seq((Nesting.Start, m)))
    }
    else {
      println("Only use % for starting a regex")
      this
    }
  }

  def >>(m: Match): SlimRegex[N] = new SlimRegex(matchers ++ Seq((Nesting.Deep, m)))

  def >(m: Match): SlimRegex[N] = new SlimRegex(matchers ++ Seq((Nesting.Direct, m)))

}

case class StrategyFromRegex[N <: Rewritable, C]() {
  def @>>(m: Match): TRegex[N, C] = new TRegex[N, C] % m
}

class Match() {
  var quantity: Quantity = Quantity(1)

  def reduceQuantity(): Option[Match] = {
    quantity match {
      case Quantity(1) => None
      case Quantity(x) if x > 1 =>
        quantity = Quantity(x - 1)
        Some(this)
      case PLUS =>
        quantity = Quantity.star
        Some(this)
      case STAR => Some(this)
      case _ => println("Invalid Quantity of Match: " + quantity); None
    }
  }

  def *(): Match = {
    quantity = STAR
    this
  }

  def +(): Match = {
    quantity = PLUS
    this
  }

  def ^(i: Int): Match = {
    quantity = Quantity(i)
    this
  }
}

case class n(r: RewritableCompanion) extends Match {
  def valid(n: Any): Boolean = r.isMyType(n)
}

case class r(r: RewritableCompanion) extends Match {
  def valid(n: Any): Boolean = r.isMyType(n)
}

case class c[N <: Rewritable](r: RewritableCompanion, acc: N => Any) extends Match {
  def valid(n: Any): Option[Any] = {
    if (r.isMyType(n)) {
      Some(acc(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class intoChild[N <: Rewritable](r: RewritableCompanion, selector: N => Any) extends Match {
  def valid(n: Any): Option[Any] = {
    if (r.isMyType(n)) {
      Some(selector(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class matchChildren[N <: Rewritable](r: RewritableCompanion, s: ChildMatch[N]*) extends Match {}

case class nP[N <: Rewritable](r: RewritableCompanion, p: N => Boolean) extends Match {
  def valid(n: Any): Boolean = {
    if (r.isMyType(n)) {
      p(n.asInstanceOf[N])
    } else {
      false
    }
  }
}

object TRegex {

  implicit def viperRegex(m: Match): SlimRegex[Node] = {
    new SlimRegex[Node] % m
  }

}


class Test {
  //val t = new TreeRegexBuilder[Node, Exp]()
  //StrategyFromRegex[Node, Exp] @>> n[Implies] > matchChildren(**).* >> n[Implies] |-> { case (o: Or, c) => Or(o.left, c.custom.head)() }

}
