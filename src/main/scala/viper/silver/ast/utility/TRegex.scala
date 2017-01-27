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

object Quantity {
  def star = Quantity(-1)

  def plus = Quantity(-2)
}

class RegexStrategy[N <: Rewritable, C](private val matchSeq: Seq[(Nesting, Match)], private val p: PartialFunction[(N, ContextC[N, Seq[C]]), N]) extends StrategyInterface[N] {

  val matchedNodes = collection.mutable.HashSet.empty[(C, N)]

  def goFurther(node: N, m: Match): Boolean = m match {
    case nodeMatch: n => nodeMatch.valid(node)
    case rewriteMatch: r => rewriteMatch.valid(node)
    case nodePredicate: nP[N] => nodePredicate.valid(node)
    case contextMatch: c[N] => contextMatch.valid(node).isDefined
    case goIntoChild: intoChild[N] => goIntoChild.valid(node).isDefined
    case _ => true
  }

  override def execute[T <: N](node: N): T = {
    // First element represents the matches, second is for having the context present in case of a rewrite match
    type RegexContext = (Seq[(Nesting, Match)], Seq[C])

    // The update function specifies if we can consume a match and go further or if we continue with the current match
    val updateFunc: PartialFunction[(N, RegexContext), RegexContext] = {
      case (node, (matches, context)) => {
        if (matches.isEmpty) {
          // If matches is empty we have nothing to do. Just return and go on
          (matches, context)
        } else {
          val nextMatch = matches.head
          var newContext = context

          // Context update done here, execute possible other actions that have to be performed in updateFunc here too
          nextMatch._2 match {
            case contextMatch: c[N] => {
              // Context update in case it is defined here
              val candContext = contextMatch.valid(node)
              if (candContext.isDefined) {
                assert(candContext.isInstanceOf[C], "Context match from regex did not return the correct type")
                newContext = newContext ++ Seq(candContext.asInstanceOf[C])
              }
            }
            case _ => {}
          }

          // Decide what happens next
          nextMatch._1 match {
            case Nesting.Direct => {
              if (goFurther(node, nextMatch._2)) {
                // Find out if we match on the current node or not
                // Match succeeded. Consume it and recurse with following matches
                (matches.drop(1), newContext)
              } else {
                // Return empty sequence because match failed. Nothing will change in further  recursion
                (Seq.empty[(Nesting, Match)], context)
              }
            }
            case Nesting.Deep | Nesting.Start => {
              if (goFurther(node, nextMatch._2)) {
                // Match succeeded. Consume it and recurse with following matches
                (matches.drop(1), newContext)
              } else {
                // Match did not succeed. Maybe it will later
                (matches, newContext)
              }
            }
          }
        }
      }
    }

    val nodesToUpdate = collection.mutable.ListBuffer.empty[(N, Seq[C])] // This hash set holds node context pairs that we will use to replace every matched node

    // This function performs actions of the according matches
    val actionFunc: (N, ContextC[N, RegexContext]) => Unit = (curNode, context) => {
      if (context.custom._1.nonEmpty) {
        // If matches is empty we have nothing to do. Just return and go on
        val nextMatch = context.custom._1.head._2
        val ctxt = context.custom._2
        nextMatch match {
          case rewriteMatch: r => {
            if (rewriteMatch.valid(curNode)) {
              nodesToUpdate.append((curNode, ctxt))
            }
          }
          case enterChild: intoChild[N] => {
            val childA = enterChild.valid(curNode)
            if (childA.isDefined) {
              assert(childA.get.isInstanceOf[N], "Child from intoChild does not extend node")
              val child = childA.get.asInstanceOf[Rewritable]
              node.getChildren foreach { n => if (child ne n.asInstanceOf[Rewritable]) context.transformer.noRec[N](child) }
            }
          }
        }
      }
    }

    val node2RewriteStrat = StrategyBuilder.ContextVisitor[N, RegexContext](actionFunc, (matchSeq, Seq.empty[C]), updateFunc)
    node2RewriteStrat.visit(node)

    //HashSet is now filled with nodes to replace. Go do it!!
    val replaceStrat = StrategyBuilder.AncestorStrategy[N]({
      case (n, c) => {
        val nodeOption = nodesToUpdate.find( _._1 eq n )
        if(nodeOption.isDefined) {
          val node2Replace = nodeOption.get
          val context = new ContextC[N, Seq[C]](c.ancestorList, node2Replace._2, c.transformer, PartialFunction.empty)
          if(p.isDefinedAt((n, context))) {
            p((n, context))
          } else {
            n
          }
        } else {
          n
        }
      }
    })

    val result = replaceStrat.execute[T](node)
    result
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

  def *(): Match = {
    quantity = Quantity.star
    this
  }

  def +(): Match = {
    quantity = Quantity.plus
    this
  }

  def ^(i: Int): Match = {
    quantity = Quantity(i)
    this
  }
}

case class n(instanceMatch:Any=>Boolean ) extends Match {
  def valid(n: Any): Boolean = instanceMatch(n)
}

case class r(instanceMatch:Any=>Boolean) extends Match {
  def valid(n: Any): Boolean = instanceMatch(n)
}

case class c[N <: Rewritable](instanceMatch:Any=>Boolean, acc: N => Any) extends Match {
  def valid(n: Any): Option[Any] = {
    if (instanceMatch(n)) {
      Some(acc(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class intoChild[N <: Rewritable](instanceMatch:Any=>Boolean, selector: N => Any) extends Match {
  def valid(n: Any): Option[Any] = {
    if (instanceMatch(n)) {
      Some(selector(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class matchChildren[N <: Rewritable](instanceMatch:Any=>Boolean, s: ChildMatch[N]*) extends Match {}

case class nP[N <: Rewritable](instanceMatch:Any=>Boolean, p: N => Boolean) extends Match {
  def valid(n: Any): Boolean = {
    if (instanceMatch(n)) {
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

  implicit def instanceMatch(r: RewritableCompanion):Any=>Boolean = {
    x => r.isMyType(x)
  }
}


class Test {
  //val t = new TreeRegexBuilder[Node, Exp]()
  //StrategyFromRegex[Node, Exp] @>> n[Implies] > matchChildren(**).* >> n[Implies] |-> { case (o: Or, c) => Or(o.left, c.custom.head)() }

}
