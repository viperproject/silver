package viper.silver.ast.utility

import viper.silver.ast.utility.Traverse.Traverse

/**
  * Created by simonfri on 05.12.2016.
  */

/**
  * An enumeration that represents traversion modes:
  * - TopDown: Perform transformation before visiting children
  * - BottomUp: Perform transformation after visiting children
  * - Innermost: Go TopDown but stop recursion after first rewrite
  * - Outermost: Go BottomUp and only rewrite first match
  */
object Traverse extends Enumeration {
  type Traverse = Value
  val TopDown, BottomUp, Innermost, Outermost = Value
}

/**
  * Trait that encapsulates all fields and Setter/Getter that are used in every Strategy
  *
  * @tparam A with Rewritable[N] Supertype of every node we want to rewrite
  */
trait StrategyInterface[A <: Rewritable] {

  protected var noRecursion = collection.mutable.HashSet.empty[Rewritable]
  protected var wasTransformed = collection.mutable.HashSet.empty[Rewritable]

  def hasChanged = wasTransformed.nonEmpty

  def transformed(node: Rewritable): Rewritable = {
    wasTransformed.add(node)
    node
  }

  def noRec[T <: A](node: Rewritable): T = {
    noRecursion.add(node)
    node.asInstanceOf[T]
  }


  def execute[T <: A](node: A): T

  def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    new ConcatinatedStrategy[A](this, s)
  }

}

object StrategyBuilder {

  def SlimStrategy[A <: Rewritable](p: PartialFunction[A, A]) = {
    new Strategy[A, SimpleContext[A]](AddArtificialContext(p)) defaultContext new NoContext[A]
  }

  def AncestorStrategy[A <: Rewritable](p: PartialFunction[(A, ContextA[A]), A], t: Traverse = Traverse.TopDown) = {
    new Strategy[A, ContextA[A]](p) defaultContext new PartialContextA[A] traverse t
  }

  def ContextStrategy[A <: Rewritable, C](p: PartialFunction[(A, ContextC[A, C]), A], default: C, updateFunc: PartialFunction[(A, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) = {
    new Strategy[A, ContextC[A, C]](p) defaultContext new PartialContextC[A, C](default, updateFunc) traverse t
  }

  def SlimVisitor[A <: Rewritable](f: A => Unit) = {
    new StrategyVisitor[A, SimpleContext[A]]({ (a: A, c: SimpleContext[A]) => f(a) })
  }

  def AncestorVisitor[A <: Rewritable](f: (A, ContextA[A]) => Unit) = {
    new StrategyVisitor[A, ContextA[A]](f) defaultContext new PartialContextA[A]
  }

  def ContextVisitor[A <: Rewritable, C](f: (A, ContextC[A, C]) => Unit, default: C, updateFunc: PartialFunction[(A, C), C] = PartialFunction.empty) = {
    new StrategyVisitor[A, ContextC[A, C]](f) defaultContext new PartialContextC[A, C](default, updateFunc)
  }

}

case class AddArtificialContext[N <: Rewritable](p: PartialFunction[N, N]) extends PartialFunction[(N, SimpleContext[N]), N] {
  override def isDefinedAt(x: (N, SimpleContext[N])): Boolean = p.isDefinedAt(x._1)

  override def apply(x: (N, SimpleContext[N])): N = p.apply(x._1)
}

class SlimStrategy[A <: Rewritable](p: PartialFunction[A, A]) extends Strategy[A, SimpleContext[A]](AddArtificialContext(p)) {}

class Strategy[A <: Rewritable, C <: Context[A]](p: PartialFunction[(A, C), A]) extends StrategyInterface[A] {
  protected var traversionMode: Traverse = Traverse.TopDown
  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty

  protected var upContext: PartialFunction[(A, _), _] = PartialFunction.empty
  protected var defaultContxt: Option[C] = None

  private var rule: RuleT[A, C] = Rule(p)

  override def transformed(node: Rewritable): A = {
    super.transformed(node)
    node.asInstanceOf[A]
  }

  def getRule = rule

  def setRule(r: RuleT[A, C]) = rule = r

  def getTraversionMode = traversionMode

  def traverse(t: Traverse): Strategy[A, C] = {
    traversionMode = t
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Strategy[A, C] = {
    recursionFunc = r
    this
  }

  def defaultContext(pC: PartialContext[A, C]): Strategy[A, C] = {
    defaultContxt = Some(pC.get(this))
    this
  }

  def +(s: Strategy[A, C]): Strategy[A, C] = {
    rule = Append[A, C](rule, s.getRule)
    this
  }

  def <(s: Strategy[A, C]): Strategy[A, C] = {
    rule = CondAppend[A, C](rule, s.getRule)
    this
  }

  def ?(s: Strategy[A, C]): PartialTernary[A, C] = {
    PartialTernary[A, C](this, s.getRule)
  }

  def repeat: RepeatedStrategy[A] = {
    new RepeatedStrategy[A](this)
  }

  def selectStrat(node: A, contextUsed: C): A = {
    wasTransformed.clear()
    traversionMode match {
      case Traverse.TopDown => executeTopDown(node, contextUsed)
      case Traverse.BottomUp => executeBottomUp(node, contextUsed)
      case Traverse.Innermost => executeInnermost(node, contextUsed)
    }
  }

  override def execute[T <: A](node: A): T = {
    assert(defaultContxt.isDefined, "Default context not set!")
    selectStrat(node, defaultContxt.get).asInstanceOf[T]
  }

  def execute[T <: A](node: A, ctxt: PartialContext[A, C]): T = {
    selectStrat(node, ctxt.get(this)).asInstanceOf[T]
  }

  /**
    * This method can be overridden to control the creation of a new node by possibly adding metadata to it
    *
    * @param old Node before transformation
    * @param now Node after transformation
    * @return Node with possibly filled in metadata or other modification
    */
  protected def preserveMetaData(old: A, now: A): A = now

  def executeTopDown(node: A, context: C): A = {

    val contextWithMyself = context.addAncestor(node).asInstanceOf[C]
    // Check which node we get from rewriting
    val newNode: A = rule.execute(node, contextWithMyself).getOrElse(node)

    // Create the new Context for children recursion
    val updatedContext: C = context.update(newNode).asInstanceOf[C]

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val res = recurseChildren(newNode, executeTopDown(_, updatedContext)) match {
      case Some(children) => transformed(newNode.duplicate(children).asInstanceOf[A])
      case None => newNode
    }
    val res2 = preserveMetaData(node, res)
    res2
  }

  def executeBottomUp(node: A, context: C): A = {
    // Add this node to context

    val updatedContext: C = context match {
      case cC: ContextC[A, _] => cC.addAncestor(node); cC.update(node).asInstanceOf[C]
      case cA: ContextA[A] => cA.addAncestor(node).asInstanceOf[C]
      case nC: SimpleContext[A] => nC.asInstanceOf[C]
    }

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newNode = recurseChildren(node, executeBottomUp(_, updatedContext)) match {
      case Some(children) =>
        transformed(node.duplicate(children).asInstanceOf[A])
      case None => node
    }

    val res = rule.execute(newNode, updatedContext).getOrElse(newNode)
    preserveMetaData(node, res)
  }

  def executeInnermost(node: A, context: C): A = {
    val newC = context.addAncestor(node).asInstanceOf[C]
    // Check which node we get from rewriting
    val maybe = rule.execute(node, newC)

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val res = if (maybe.isEmpty) {

      recurseChildren(node, executeInnermost(_, newC)) match {
        case Some(children) => transformed(node.duplicate(children).asInstanceOf[A])
        case None => node
      }
    } else {
      maybe.get
    }

    preserveMetaData(node, res)
  }


  /**
    * Following methods are helper methods for the other Strategy implementations
    */
  protected def recurseChildren(node: A, recurse: A => A): Option[Seq[Any]] = {
    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children = node.getChildren

    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = recursionFunc.applyOrElse(node, (node: A) => {
      children.indices map { x => true }
    })
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length == children.length, "Incorrect number of children in recursion")

    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val newChildren: Seq[Any] = children.zip(childrenSelect) map {
      case (o: Option[Rewritable], true) => o match {
        case None => None
        case Some(x: Rewritable) => if (!noRecursion.contains(x)) Some(recurse(x.asInstanceOf[A])) else x
      }
      case (s: Seq[Rewritable], true) => s map { x => if (!noRecursion.contains(x)) recurse(x.asInstanceOf[A]) else x }
      case (n: Rewritable, true) => if (!noRecursion.contains(n)) recurse(n.asInstanceOf[A]) else n
      case (old, false) => old
    }


    val hasChanged: Boolean = newChildren.foldLeft(false)((b1, elem) => {
      val b2 = elem match {
        case seq: Seq[Rewritable] => seq.map {
          wasTransformed.contains(_)
        }.fold(false)(_ || _)
        case opt: Option[Rewritable] => opt match {
          case Some(x) => wasTransformed.contains(x)
          case None => false // No empty child can be generated from existing child => if None is new child it was already None in old child => no change
        }
        case node: Rewritable => wasTransformed.contains(node)
      }
      b1 || b2
    })

    if (hasChanged) {
      Some(newChildren)
    } else {
      None
    }
  }
}

/**
  * This class encapsulates strategies that are appended. The execute method executes them one after another and gives the resulting node of a transformation
  * as an argument for the next node
  *
  * @param s1 strategy 1
  * @param s2 strategy 2
  */
class ConcatinatedStrategy[A <: Rewritable](s1: StrategyInterface[A], val s2: StrategyInterface[A]) extends StrategyInterface[A] {
  private var strategies = collection.mutable.ListBuffer.empty[StrategyInterface[A]]

  strategies.append(s1)
  strategies.append(s2)


  override def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    strategies.append(s)
    this
  }

  def ||(s: ConcatinatedStrategy[A]): ConcatinatedStrategy[A] = {
    strategies ++= s.strategies
    this
  }

  override def execute[T <: A](node: A): T = strategies.foldLeft(node)((n, strat) => strat.execute[A](n)).asInstanceOf[T]

  override def hasChanged: Boolean = s1.hasChanged || s2.hasChanged
}

class RepeatedStrategy[A <: Rewritable](s: StrategyInterface[A]) extends StrategyInterface[A] {
  override def execute[T <: A](node: A): T = {
    val result: T = s.execute[T](node)
    if (!s.hasChanged) {
      result
    } else {
      execute[T](result)
    }
  }

  def execute[T <: A](node: A, i: Int): A = {
    if (i <= 0) node

    val result = s.execute[T](node)
    if (s.hasChanged) {
      result
    } else {
      execute[T](result, i - 1)
    }
  }

  override def ||(s: StrategyInterface[A]): ConcatinatedStrategy[A] = {
    new ConcatinatedStrategy[A](this, s)
  }

  override def hasChanged: Boolean = s.hasChanged
}


trait Context[A <: Rewritable] {
  def transformer: StrategyInterface[A]

  def addAncestor(node: A): Context[A]

  def replaceNode(node: A): Context[A]

  def update(node: A): Context[A]
}

class SimpleContext[A <: Rewritable](val transformer: StrategyInterface[A]) extends Context[A] {
  override def addAncestor(node: A): SimpleContext[A] = this

  override def replaceNode(node: A): SimpleContext[A] = this

  override def update(node: A): SimpleContext[A] = this
}

/**
  * This class holds ancestor information about the current node
  *
  * @param ancestorList List of all ancestors
  */
class ContextA[A <: Rewritable](val ancestorList: Seq[A], val transformer: StrategyInterface[A]) extends Context[A] {

  def addAncestor(n: A): ContextA[A] = {
    new ContextA[A](ancestorList ++ Seq(n), transformer)
  }

  override def replaceNode(n: A): ContextA[A] = {
    new ContextA[A](ancestorList.dropRight(1) ++ Seq(n), transformer)
  }

  override def update(n: A): ContextA[A] = {
    replaceNode(n)
  }

  lazy val node = ancestorList.last

  /**
    * The predecessor child of the parent that follows the node itself
    */
  lazy val previous: Option[Any] = predecessors.lastOption

  /**
    * All children of the parent of a node that precede the node itself
    */
  lazy val predecessors: Seq[Any] = family.takeWhile(!isEqualNode(_))

  /**
    * The successor child of the parent that follows the node itself
    */
  lazy val next: Option[Any] = successors.headOption

  /**
    * All children of the parent of a node that follow the node itself
    */
  lazy val successors: Seq[Any] = family.dropWhile(!isEqualNode(_)).drop(1)


  /**
    * All children of the parent without the node itself
    */
  lazy val siblings: Seq[Any] = family.filter(!isEqualNode(_))


  /**
    * All children of the parent. Sequence of nodes and options of nodes will be unfolded and the node itself is included in the list
    */
  lazy val family: Seq[Any] = parent.getChildren.foldLeft(Seq.empty[Any])((children: Seq[Any], y: Any) => y match {
    case elem: Seq[A] => children ++ elem
    case elem: Option[A] => children ++ (elem match {
      case Some(x) => Seq(x)
      case None => Seq.empty[Any]
    })
    case elem => children ++ Seq(elem)
  })
  /**
    * Parent of node
    */
  lazy val parent: A = ancestorList.dropRight(1).last

  def isEqualNode(elem: Any): Boolean = elem match {
    case Some(x: AnyRef) => x eq node.asInstanceOf[AnyRef]
    case Seq(_) => false
    case p: AnyRef => p eq node.asInstanceOf[AnyRef]
  }

}

class ContextC[A <: Rewritable, C](aList: Seq[A], val custom: C, override val transformer: StrategyInterface[A], val upContext: PartialFunction[(A, C), C]) extends ContextA[A](aList, transformer) {
  override def addAncestor(n: A): ContextC[A, C] = {
    new ContextC(ancestorList ++ Seq(n), custom, transformer, upContext)
  }

  override def replaceNode(n: A): ContextC[A, C] = {
    new ContextC(ancestorList.dropRight(1) ++ Seq(n), custom, transformer, upContext)
  }

  def updateCustom(): ContextC[A, C] = {
    val cust = if (upContext.isDefinedAt((node, custom))) upContext(node, custom) else custom
    new ContextC[A, C](ancestorList, cust, transformer, upContext)
  }

  override def update(n: A): ContextC[A, C] = {
    replaceNode(n).updateCustom()
  }
}

trait PartialContext[A <: Rewritable, C <: Context[A]] {
  def get(transformer: StrategyInterface[A]): C
}

class NoContext[A <: Rewritable] extends PartialContext[A, SimpleContext[A]] {
  override def get(transformer: StrategyInterface[A]): SimpleContext[A] = new SimpleContext[A](transformer)
}

class PartialContextA[A <: Rewritable](val aList: Seq[A] = Seq()) extends PartialContext[A, ContextA[A]] {
  override def get(transformer: StrategyInterface[A]): ContextA[A] = new ContextA[A](aList, transformer)
}

class PartialContextC[A <: Rewritable, C](val custom: C, val upContext: PartialFunction[(A, C), C] = PartialFunction.empty, val aList: Seq[A] = Seq()) extends PartialContext[A, ContextC[A, C]] {
  def get(list: Seq[A], upC: PartialFunction[(A, C), C], transformer: StrategyInterface[A]): ContextC[A, C] = new ContextC[A, C](list, custom, transformer, upC)

  def get(list: Seq[A], transformer: StrategyInterface[A]): ContextC[A, C] = get(list, upContext, transformer)

  override def get(transformer: StrategyInterface[A]): ContextC[A, C] = get(aList, transformer)
}


class StrategyVisitor[A <: Rewritable, C <: Context[A]](val visitNode: (A, C) => Unit) extends StrategyInterface[A] {


  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty
  protected var defaultContxt: Option[C] = None


  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): StrategyVisitor[A, C] = {
    recursionFunc = r
    this
  }

  def defaultContext(pC: PartialContext[A, C]): StrategyVisitor[A, C] = {
    defaultContxt = Some(pC.get(this))
    this
  }

  override def execute[T <: A](node: A): T = {
    assert(defaultContxt.isDefined, "Default context not set!")
    visitContext(node, defaultContxt.get)
    node.asInstanceOf[T]
  }


  def visit(node: A):Unit = {
    execute[A](node)
  }

  def visitContext(node: A, context: C): Unit = {

    val contextWithMyself = context.addAncestor(node).asInstanceOf[C]
    // Check which node we get from rewriting
    visitNode(node, contextWithMyself)

    // Create the new Context for children recursion
    val updatedContext: C = context.update(node).asInstanceOf[C]

    val children = node.getChildren

    val childrenSelect = if (recursionFunc.isDefinedAt(node)) {
      recursionFunc(node)
    } else {
      children.indices map { x => true }
    }

    children.zip(childrenSelect) foreach {
      case (child, b) => if (b) {
        child match {
          case o: Option[Rewritable] => o match {
            case None => None
            case Some(node: Rewritable) => if (!noRecursion.contains(node)) visitContext(node.asInstanceOf[A], updatedContext)
          }
          case s: Seq[Rewritable] => s foreach { x => if (!noRecursion.contains(x)) visitContext(x.asInstanceOf[A], updatedContext) }
          case n: Rewritable => if (!noRecursion.contains(n)) visitContext(n.asInstanceOf[A], updatedContext)
        }
      }
    }
  }


}

class Query[A <: Rewritable, B](val getInfo: PartialFunction[A, B]) {

  protected var accumulator: Seq[B] => B = (x: Seq[B]) => x.head
  protected var nElement: Option[B] = None

  def getAccumulator = accumulator

  def accumulate(a: Seq[B] => B): Query[A, B] = {
    accumulator = a
    this
  }

  protected var recursionFunc: PartialFunction[A, Seq[Boolean]] = PartialFunction.empty

  def getNeutralElement = nElement

  def neutralElement(ne: B): Query[A, B] = {
    nElement = Some(ne)
    this
  }

  def recurseFunc(r: PartialFunction[A, Seq[Boolean]]): Query[A, B] = {
    recursionFunc = r
    this
  }

  // Query only makes sense top down
  def execute(node: A): B = {
    // Check which node we get from rewriting
    val qResult: B = if (getInfo.isDefinedAt(node)) {
      getInfo(node)
    } else {
      assert(nElement.isDefined, "Node " + node + "does not define a result. Either define it in query or specify neutral element")
      nElement.get
    }

    // Put all the children of this node into a sequence
    // First try to get children form the user defined function cChildren in case we have a special case here
    // Otherwise get children from the product properties, but only those that are a subtype of A and therefore form the Tree
    val children = node.getChildren


    // Get the indices of the sequence that we perform recursion on and check if it is well formed. Default case is all children
    val childrenSelect = if (recursionFunc.isDefinedAt(node)) {
      recursionFunc(node)
    } else {
      children.indices map { x => true }
    }
    // Check whether the list of indices is of correct length
    assert(childrenSelect.length == children.length, "Incorrect number of children in recursion")


    // Recurse on children if the according bit (same index) in childrenSelect is set. If it is not set, leave child untouched
    val seqResults: Seq[Option[B]] = children.zip(childrenSelect) collect {
      case (child, b) => if (b) {
        child match {
          case o: Option[Rewritable] => o match {
            case None => None
            case Some(node: Rewritable) => Some(execute(node.asInstanceOf[A]))
          }
          case s: Seq[Rewritable] => Some(accumulator(s map { x => execute(x.asInstanceOf[A]) }))
          case n: Rewritable => Some(execute(n.asInstanceOf[A]))
        }
      } else {
        None
      }
    }
    accumulator(Seq(qResult) ++ (seqResults collect { case Some(x: B) => x }))
  }

}


// ------------------------------------------------------------------------- Composition Code here -------------------------------------------------------------------------------------------------

/**
  * A trait that is used for providing an interface for rules. We need the contravariance parameter to create the relationship:
  * RuleC < RuleA < Rule that proves helpful when combining those rules
  */
private[utility] trait RuleT[A <: Rewritable, C <: Context[A]] {
  def execute(node: A, context: C): Option[A]
}

/**
  * RuleC lifts a partial function to a rule that is used in StrategyC
  *
  * @param r The partial function
  */
private case class Rule[A <: Rewritable, C <: Context[A]](r: PartialFunction[(A, C), A]) extends RuleT[A, C] {
  override def execute(node: A, context: C): Option[A] = {
    if (r.isDefinedAt(node, context)) {
      val res = r((node, context))
      context.transformer.transformed(res)
      Some(res)
    } else {
      None
    }
  }
}

/**
  * Class Append takes two rules and executes them one after another
  *
  * @param r1 First rule
  * @param r2 Second rule
  */
private case class Append[A <: Rewritable, C <: Context[A]](r1: RuleT[A, C], r2: RuleT[A, C]) extends RuleT[A, C] {

  override def execute(node: A, context: C): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.replaceNode(res1.get).asInstanceOf[C])
      if (res2.isDefined) res2 else res1
    } else {
      r2.execute(node, context)
    }
  }
}

/**
  * CondAppend takes two rules as parameter. If r1 is defined on a node it will execute both otherwise nothing
  *
  * @param r1 First rule
  * @param r2 Second rule
  *
  */
private case class CondAppend[A <: Rewritable, C <: Context[A]](r1: RuleT[A, C], r2: RuleT[A, C]) extends RuleT[A, C] {

  override def execute(node: A, context: C): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.replaceNode(res1.get).asInstanceOf[C])
      if (res2.isDefined) res2 else res1
    }
    else {
      None
    }
  }
}

/**
  * Ternary takes three rules as parameter. If r1 is defined on a node it will execute r1 and r2 otherwise r3
  *
  * @param r1 Rule for condition
  * @param r2 Rule in case defined
  * @param r3 Rule in case not defined
  */
private case class Ternary[A <: Rewritable, C <: Context[A]](r1: RuleT[A, C], r2: RuleT[A, C], r3: RuleT[A, C]) extends RuleT[A, C] {

  override def execute(node: A, context: C): Option[A] = {
    val res1 = r1.execute(node, context)
    if (res1.isDefined) {
      val res2 = r2.execute(res1.get, context.replaceNode(node).asInstanceOf[C])
      if (res2.isDefined) res2 else res1
    } else {
      val res3 = r3.execute(node, context)
      if (res3.isDefined) res3 else res1
    }
  }
}

// Three partial ternary classes one for each strategy to make it typesafe
case class PartialTernary[A <: Rewritable, C <: Context[A]](s: Strategy[A, C], r2: RuleT[A, C]) {
  def |(s2: Strategy[A, C]): Strategy[A, C] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }
}