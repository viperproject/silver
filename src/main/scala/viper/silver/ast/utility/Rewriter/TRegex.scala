package viper.silver.ast.utility.Rewriter

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._
import viper.silver.ast.utility._

import scala.language.implicitConversions
import scala.reflect.api
import scala.reflect.runtime.universe._


// Core of the Regex AST
trait Match {
  def createAutomaton(): TRegexAutomaton
}

// Matches on nodes directly
class NMatch[N <: Rewritable : TypeTag](val pred: N => Boolean, val rewrite: Boolean) extends Match {

  // Im not happy with this method. It is basically: n.isInstanceOf[N] that works around type erasure
  def matches[T: TypeTag](n: T):Boolean = {
    // TODO: This code works but im not really familiar with reflection. Is there a better solution?
    val mirror = runtimeMirror(n.getClass.getClassLoader)  // obtain runtime mirror
    val sym = mirror.staticClass(n.getClass.getName)  // obtain class symbol for `n`
    val tpe = sym.selfType  // obtain type object for `n`

    // create a type tag which contains above type object
    val t1 = TypeTag(mirror, new api.TypeCreator {
      def apply[U <: api.Universe with Singleton](m: api.Mirror[U]) =
        if (m eq mirror) tpe.asInstanceOf[U # Type]
        else throw new IllegalArgumentException(s"Type tag defined in $mirror cannot be migrated to other mirrors.")
    }).tpe


    val t2 = typeOf[N]
    val bres =  t1 <:< t2
    bres
  }

  def holds(node: Rewritable): Boolean = {
    if (matches(node)) {
      pred(node.asInstanceOf[N])
    } else {
      false
    }
  }

  override def createAutomaton() = {
    val start = new State
    val end = new State

    start.setMTrans(end, this)
    new TRegexAutomaton(start, end)
  }

  def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = Seq.empty[TransitionInfo] ++ (if(rewrite) Seq(MarkedForRewrite()) else Nil)

}

class ContextNMatch[N <: Rewritable : TypeTag](c: N => Any, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  override def getTransitionInfo(n: Rewritable) = {
    Seq(ContextInfo(c(n.asInstanceOf[N]))) ++ (if(rewrite) Seq(MarkedForRewrite()) else Nil)
  }
}

class ChildSelectNMatch[N <: Rewritable : TypeTag](ch: N => Rewritable, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  override def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = {
    Seq(ChildSelectInfo(ch(n.asInstanceOf[N]))) ++ (if(rewrite) Seq(MarkedForRewrite()) else Nil)
  }
}

// Combine node matches together
abstract class CombinatorMatch(val m1: Match, val m2: Match) extends Match

class OrMatch(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    val start = new State
    val end = new State

    start.addETrans(a1.start)
    start.addETrans(a2.start)
    a1.end.addETrans(end)
    a2.end.addETrans(end)

    new TRegexAutomaton(start, end)
  }
}

// Put the two automatas one after the other
class Nested(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    a1.end.addETrans(a2.start)
    new TRegexAutomaton(a1.start, a2.end)
  }
}

// Allow to skip or iterate on the automaton indefinitely
class Star(m: Match) extends Match {
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()
    val out = new State

    a.start.addETrans(out)
    a.end.addETrans(a.start)

    new TRegexAutomaton(a.start, out)
  }
}

// 0 or 1 occurence. Simply connect start node with end node with an epsilon transformation.
class Questionmark(m: Match) extends Match {
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()

    val start = a.start
    val end = a.end
    start.addETrans(end)

    a
  }

}

class TreeRegexBuilder[N <: Rewritable, COLL](val accumulator:(COLL, COLL)=>COLL, val comparator:(COLL, COLL)=>Boolean, default: COLL) {
  def &>(f: FrontendRegex) = new TreeRegexBuilderWithMatch[N, COLL](accumulator, comparator, f, default)
}

class TreeRegexBuilderWithMatch[N <: Rewritable, COLL](val accumulator:(COLL, COLL) => COLL, val comparator:(COLL, COLL)=>Boolean, regex: FrontendRegex, default: COLL) {
  def |->(p: PartialFunction[(N, RegexContext[N, COLL]), N]) = new RegexStrategy[N, COLL](regex.getAST.createAutomaton(), p, new PartialContextR(default, accumulator, comparator))
}

object TreeRegexBuilder {
  def context[N <: Rewritable, COLL](accumulator: (COLL, COLL) => COLL, comparator: (COLL, COLL)=>Boolean, default: COLL) = new TreeRegexBuilder[N, COLL](accumulator, comparator, default)
  def simple[N <: Rewritable] = new TreeRegexBuilder[N, Any]( (x, y) => x, (x,y)=> true, 1)
}


// Frontend of the Regex AST
trait FrontendRegex {
  def getAST: Match

  def >>(m: FrontendRegex) = DeepNestedF(this, m)

  def >(m: FrontendRegex) = NestedF(this, m)

  def ? = QuestionmarkF(this)

  def * = StarF(this)

  def ** = DoubleStarF(this)

  def + = PlusF(this)

  def |(m: FrontendRegex) = OrF(this, m)

}

// Simple node match
case class n[N <: Rewritable : TypeTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, false)
}

// Match node in case predicate holds
case class nP[N <: Rewritable : TypeTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}

// Match node and mark rewritable
case class r[N <: Rewritable : TypeTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, true)
}

// Match node and mark rewritable in case predicate holds
case class rP[N <: Rewritable : TypeTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}


// match context
case class c[N <: Rewritable : TypeTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, false)
}

// match context and mark node for rewriting
case class cr[N <: Rewritable : TypeTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, true)
}

// match context in case predicate holds
case class cP[N <: Rewritable : TypeTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, false)
}

// match context in case predicate holds and mark node for rewriting
case class cPr[N <: Rewritable : TypeTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, true)
}

// match node and select the child for futher recursion
case class inCh[N <: Rewritable : TypeTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, false)
}

// match node and select the child for futher recursion and mark as rewritable
case class iCr[N <: Rewritable : TypeTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, true)
}

// match node in case predicate holds and select the child for futher recursion
case class inChP[N <: Rewritable : TypeTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, predicate, false)
}

// match node in case predicate holds and select the child for futher recursion and mark as rewritable
case class inChPr[N <: Rewritable : TypeTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, predicate, true)
}


case class StarF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Star(m.getAST)
}

case class DoubleStarF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Star(new Nested(m.*.getAST, n[Rewritable].*.getAST))
}

case class PlusF(m: FrontendRegex) extends FrontendRegex {
  // Reduction: a+ == a > a*
  override def getAST: Match = new Nested(m.getAST, m.*.getAST)
}

case class QuestionmarkF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Questionmark(m.getAST)
}

case class NestedF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Nested(m1.getAST, m2.getAST)
}

case class OrF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new OrMatch(m1.getAST, m2.getAST)
}

case class DeepNestedF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  // a >> b == a > _* > b
  override def getAST: Match = new Nested(new Nested(m1.getAST, n[Rewritable].*.getAST), m2.getAST)
}

class Test {
  c[QuantifiedExp](_.variables).** >> nP[Or](_.left eq TrueLit()())
}





class RegexContext[A <: Rewritable, COLL](aList: Seq[A], val c: COLL, transformer: StrategyInterface[A], val upContext: (COLL, COLL) => COLL, val comp:(COLL, COLL)=>Boolean) extends ContextA[A](aList, transformer) {
  override def addAncestor(n: A): RegexContext[A, COLL] = {
    new RegexContext(ancestorList ++ Seq(n), c, transformer, upContext, comp)
  }

  override def replaceNode(n: A): RegexContext[A, COLL] = {
    new RegexContext(ancestorList.dropRight(1) ++ Seq(n), c, transformer, upContext, comp)
  }

  def update(con: COLL): RegexContext[A, COLL] = {
    new RegexContext(ancestorList, upContext(c, con), transformer, upContext, comp)
  }

  def compare(other: RegexContext[A, COLL]): Boolean = {
    comp(this.c, other.c)
  }
}

class PartialContextR[A <: Rewritable, COLL](val c: COLL, val upContext: (COLL, COLL) => COLL, val comp:(COLL, COLL)=>Boolean) extends PartialContext[A, ContextA[A]] {
  def get(anc: Seq[A], transformer: StrategyInterface[A]): RegexContext[A, COLL] = new RegexContext[A, COLL](anc, c, transformer, upContext, comp)
  override def get(transformer: StrategyInterface[A]): RegexContext[A, COLL] = new RegexContext[A, COLL](Seq(), c, transformer, upContext, comp)
}


class RegexStrategy[N <: Rewritable, COLL](a: TRegexAutomaton, p: PartialFunction[(N, RegexContext[N, COLL]), N], default: PartialContextR[N, COLL]) extends Strategy[N, RegexContext[N, COLL]](p) {
  type CTXT = RegexContext[N, COLL]

  override def transformed(node: Rewritable): N = {
    super.transformed(node)
    node.asInstanceOf[N]
  }

  // Custom data structure for keeping the node context pairs
  class MatchSet {
    var map = collection.mutable.ListBuffer.empty[(N, CTXT)]

    def put(tuple: (N, CTXT)) = {
      val node = tuple._1
      val context = tuple._2
      map.zipWithIndex.find( _._1._1 eq node) match {
        case None => map.append((node, context))
        case Some(tup) =>
          val better = (node, if (tup._1._2.compare(context)) tup._1._2 else context)
          map.remove(tup._2)
          map.append(better)
      }
    }

    def get(node: N): Option[CTXT] = {
      map.find( _._1 eq node) match {
        case None => None
        case Some(t) => Some(t._2)
      }
    }

  }



  override def execute[T <: N](node: N): T = {
    // Store found matches here
    val matches = new MatchSet

    // Recursively matches on the AST by iterating through the automaton
    def recurse(n: N, s:State, ctxt:CTXT,  marked:Seq[(N, CTXT)]): Unit = {
      // Base case: if we reach accepting state we matched and can add all marked nodes to the list
      if(s.isAccepting) {
        marked.foreach( matches.put )
        return
      }

      // Perform possible transition and obtain actions.
      // If no transition is possible (error state) states will be empty after this call and the recursion will stop
      val (states, action) = s.performTransition(n)

      // Get all the children to recurse further
      val children: Seq[Rewritable] = n.getChildren.foldLeft( Seq.empty[Rewritable] )({
        case (seq, o: Option[Rewritable]) => o match {
          case None => seq
          case Some(x: Rewritable) => seq ++ Seq(x)
        }
        case (seq, s: Seq[Rewritable]) => seq ++ s
        case (seq, r: Rewritable) => seq ++ Seq(r)
        case (seq, _) => seq
      })

      // Actions may or may not change marked nodes, children or context
      var newMarked = marked
      var newChildren = children
      var newCtxt = ctxt.addAncestor(n)

      // Apply actions
      action foreach {
        // Marked for rewrite TODO: error handling in case node casting fails
        case MarkedForRewrite() => newMarked = newMarked ++ Seq((n.asInstanceOf[N], newCtxt))
        // Context update TODO: error handling in case context casting fails
        case ContextInfo(c:Any) => newCtxt = ctxt.update(c.asInstanceOf[COLL])
        // Only recurse if we are the selected child
        case ChildSelectInfo(r:Rewritable) => newChildren.filter( _ eq r )
      }

      // Perform further recursion for each child and for each state
      newChildren.foreach( child => {
        states.foreach( state => {
          recurse(child.asInstanceOf[N], state, newCtxt, newMarked )
        })
      })
    }

    // Use the recurse function to match paths that start at a point where the first pattern matches
    val startStates = a.start.effective
    val visitor = StrategyBuilder.AncestorStrategy[N]( {case (n,c) => {
      // Start recursion if any of the start states is valid for recursion
      startStates.foreach( s => {
        if(s.isValidInput(n))
        recurse(n, s, default.get(c.ancestorList.dropRight(1), this), Seq.empty[(N, CTXT)])
      } )
      n
    }})

    visitor.execute(node)

    val result = replaceTopDown(node, matches)
    result.asInstanceOf[T]
  }

  // Replace matches with product nodes
  def replaceTopDown(n: N, matches: MatchSet): N = {
    // Find out if this node is going to be replaced
    val replaceInfo = matches.get(n)

    // get resulting node from rewriting
    val resultNode = replaceInfo match {
      case None => n
      case Some(elem) => transformed(p(n, elem))
    }

    val res = recurseChildren(resultNode, replaceTopDown(_, matches)) match {
      case Some(children) => transformed(resultNode.duplicate(children).asInstanceOf[N])
      case None => resultNode
    }
    val res2 = preserveMetaData(n, res)
    res2
  }
}