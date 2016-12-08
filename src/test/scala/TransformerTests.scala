/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver

import scala.language.implicitConversions
import org.scalatest.{FunSuite, Matchers}
import ast._
import ast.utility.{Recurse, Strategy, StrategyC, Traverse, Transformer}
import ast.If

class TransformerTests extends FunSuite with Matchers {
  test("Implication into Disjunction") {
    // Create new strategy. Parameter is the partial function that is applied on all nodes
    val strat = new Strategy[Node]({
      case Implies(left, right) => Or(Not(left)(), right)()
    }) defineDuplicator Transformer.viperDuplicator traverse Traverse.TopDown recurse Recurse.All

    // Example of how to execute the strategy with a dummy node
    var targetNode: Node = Div(0, 0)()
    var res = strat.execute(targetNode)
    println(targetNode.toString())
    println(res.toString())


    targetNode = Assert(Implies(TrueLit()(),TrueLit()())())()
    res = strat.execute(targetNode)
    println(targetNode.toString())
    println(res.toString())





    TrueLit()() should be (TrueLit()())
  }
/*
  test("while loop into if & goto") {
    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    val strat = new Strategy[Node]({
      case w: While =>
        val invars: Exp = w.invs.reduce((x: Exp, y: Exp) => And(x, y)())
        Seqn(Seq(
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(Not(w.cond)(w.cond.pos, w.cond.info), Goto("Skiploop")(w.pos, w.info), Label("NoOp")(w.pos, w.info))(w.pos, w.info),
          Label("Loop")(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(w.cond, Goto("Loop")(w.pos, w.info), Label("NoOp")(w.pos, w.info))(w.pos, w.info),
          Label("Skiploop")(w.pos, w.info)
        ))(w.pos, w.info)

    }) traverse Traverse.Innermost recurse Recurse.All
  }

  test("Disjunctions to Inhale/Exhale") {
    // This the example from my initial presentation slides
    // Context c holds all ancestors of the current node
    val strat = new StrategyC[Node, Seq[LocalVarDecl]]({
      case (Or(l, r), c) =>
        //val nonDet = NonDet(c, Bool) Cannot use this (silver angelic)
        InhaleExhaleExp(CondExp(TrueLit()(), l, r)(), Or(l, r)())() // Placed true lit instead of nonDet
    }) updateContext {
      case q:QuantifiedExp => q.variables
    } traverse Traverse.TopDown recurse Recurse.All recurseFunc {
      case i: InhaleExhaleExp => Seq(true, false)
    }
  }

  test("Fold many consecutive assertions into one assert") {
    // I chose arbitrarily that every combined assert has the position and info of any assert. This is probably not what we want but i don't care here
    val strat = new Strategy[Node]({
      case (a: Assert, c) =>
        // TODO implement sibling stuff here
        c match {
          case s: Seqn =>
            val predecessors = s.take(s.toIndexedSeq.indexOf(a)) // All nodes before a in the sequence

            predecessors.last match {
              case x: Assert => Label("NoOp")() // NoOp?
              case _ =>
                // Take all following assertions and put them together into one assertion
                // Take all statements behind a     // Take all successors that are assertions until one is no assertion // Transform them into actual assertion type
                val successorAssertions: Seq[Assert] = s.drop(s.toIndexedSeq.indexOf(a) + 1).takeWhile({ case x: Assert => true case _ => false }).collect({ case i: Assert => i }).toSeq

                // Put everyting together
                successorAssertions.reduce((x: Assert, y: Assert) => Assert(And(x.exp, y.exp)())(x.pos, x.info))


              case _ => a
            }
        }
    })
  }

  test("Replace Method Calls") {
    // Combination of three transformations
    // 1. Replace method calls with precondition, postcondition
    // 2. Replace parameter with just the parameter in postcondition
    // 3. Replace parameters/results with arguments/targets in precondition/postconditions


    val strat = new Strategy[Node]({
      case m: MethodCall =>
        val mDecl: Method = null // How do i get the method declaration from a method call? :(

        val replacePre = new Strategy[Exp]({
          case l: LocalVar =>
            mDecl.formalArgs.find((x) => x.name == l.name) match {
              case Some(x) =>
                val i = mDecl.formalArgs.indexOf(x)
                m.args(i)
              case None => l
            }

        })

        val replaceOld = new Strategy[Exp]({
          case o: Old => o.exp

        })
        // Here position and info will be changed anyway with the other transformation

        val replacePost = new Strategy[Exp]({
          case l: LocalVarDecl =>
            mDecl.formalReturns.find((x) => x.name == l.name) match {
              case Some(x) =>
                val i = mDecl.formalReturns.indexOf(x)
                m.targets(i)
              case None => l
            }
        })



        val pres = replacePre.execute(mDecl.pres.reduce((x, y) => And(x, y)()))
        val posts = replacePost.execute(replacePre.execute(replaceOld.execute(mDecl.posts.reduce((x, y) => And(x, y)()))))
        Seqn(Seq(
          Exhale(pres)(),
          Inhale(posts)()
        ))()


    }) traverse Traverse.Innermost
  }
*/
  implicit def int2IntLit(i: Int): IntLit = IntLit(i)()

}
