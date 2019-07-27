// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter
import viper.silver.ast.utility.rewriter.Traverse.Traverse
import scala.collection.mutable
import scala.reflect.runtime.{universe => reflection}

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
  * Trait that encapsulates information and functionality for all Strategy types
  *
  * @tparam N Type of the AST nodes
  */
trait StrategyInterface[N <: Rewritable] {

  // Store every special node we don't want to recurse on
  // A hash set would be more efficient but then we get problems with circular dependencies (calculating hash never terminates)

  protected val noRecursion = mutable.ListBuffer.empty[NodeEq]

  case class NodeEq(node: Rewritable) {
    override def equals(that: Any): Boolean = that match {
      case req: NodeEq => this.node eq req.node
      case ref: AnyRef => this.node eq ref
      case _ => false
    }
  }

  protected var changed = false

  /**
    * A flag that indicates whether the last AST transformed by this transformer was changed
    *
    * @return
    */
  def hasChanged: Boolean = changed

  /**
    * Prevent recursion on special nodes
    *
    * @param node node to prevent recursion on
    * @tparam T type of the node
    * @return return the node again (convenience)
    */
  def noRec[T <: N](node: Rewritable): T = {
    noRecursion.append(NodeEq(node))
    node.asInstanceOf[T]
  }

  /**
    * Execute strategy on AST
    *
    * @param node root node of the AST
    * @tparam T type of the rewritten root
    * @return rewritten root
    */
  def execute[T <: N](node: N): T

  /**
    * Append two strategies. `s` is executed after `this` has finished
    *
    * @param s strategy to combine with
    * @return combined strategy
    */
  def ||(s: StrategyInterface[N]): ConcatenatedStrategy[N] = {
    new ConcatenatedStrategy[N](this, s)
  }

  /** This method can be overridden to control the creation of a new node by possibly adding
    * metadata to it.
    *
    * @param old Node before rewriting
    * @param now Node after rewriting
    * @param directlyRewritten Indicates if `now` was obtained from `old` by rewriting `old` itself,
    *                          or if `old` was merely duplicated because its children were
    *                          rewritten.
    * @return Updated node that will be built into the AST
    */
  protected def preserveMetaData(old: N, now: N, directlyRewritten: Boolean): N = now
}

/**
  * Factory object for often used Strategy and Visitor settings
  */
object StrategyBuilder {

  /**
    * Create a strategy without context just node to node
    *
    * @param p Partial function that transforms the input node into the output node
    * @param t Traverse direction
    * @tparam N Common supertype of every node in the tree
    * @return Strategy object ready to execute on a tree
    */
  def Slim[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag](p: PartialFunction[N, N], t: Traverse = Traverse.TopDown) = {
    new SlimStrategy[N](p) defaultContext new NoContext[N] traverse t
  }

  /**
    * Strategy that allows access to ancestors and siblings
    *
    * @param p Partial function that transforms input (node, context) into a new node
    * @param t Traverse direction
    * @tparam N Common supertype of every node in the tree
    * @return Strategy object ready to execute on a tree
    */
  def Ancestor[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag](p: PartialFunction[(N, ContextA[N]), N], t: Traverse = Traverse.TopDown) = {
    new Strategy[N, ContextA[N]](p) defaultContext new PartialContextA[N] traverse t
  }

  /**
    * Strategy that allows access to ancestors, siblings and a custom defined context
    *
    * @param p          Partial function that transforms input (node, context) into a new node
    * @param default    Default context value (in case no context is present)
    * @param updateFunc Function that extracts context out of nodes and combines it with existing context
    * @param t          Traversal direction
    * @tparam N Common supertype of every node in the tree
    * @tparam C Type of the context
    * @return Strategy object ready to execute on a tree
    */
  def Context[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, C](p: PartialFunction[(N, ContextC[N, C]), N], default: C, updateFunc: PartialFunction[(N, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) = {
    new Strategy[N, ContextC[N, C]](p) defaultContext new PartialContextC[N, C](default, updateFunc) traverse t
  }

  /**
    * Strategy that allows access to custom defined context (of parameter type C)
    *
    * @param p          Partial function that transforms input (node, context) into a new node
    * @param default    Default context value (in case no context is present)
    * @param updateFunc Function that extracts context out of nodes and combines it with existing context
    * @param t          Traversal direction
    * @tparam N Common supertype of every node in the tree
    * @tparam C Type of the context
    * @return Strategy object ready to execute on a tree
    */
  def CustomContext[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, C](p: PartialFunction[(N, C), N], default: C, updateFunc: PartialFunction[(N, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) = {
    new Strategy[N, ContextCustom[N,C]]({ // rewrite partial function taking context with parent access etc. to one just taking the custom context
      case (n, context) if p.isDefinedAt(n, context.c) => p.apply(n, context.c)
    }).defaultContext(new PartialContextCC[N,C](default,updateFunc)) traverse t
  }

  /**
    * Strategy that allows both node and context to be rewritten.
    *
    * @param p          Partial function that transforms input (node, context) into a new (node, context)
    * @param default    Initial context
    * @param t          Traversal order
    * @tparam N         Common supertype of every node in the tree
    * @tparam C         Type of the context
    * @return           Strategy object ready to execute on a tree
    */
  def RewriteNodeAndContext[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, C](p: PartialFunction[(N, C), (N, C)], default: C, t: Traverse = Traverse.TopDown) = {
    val p1: PartialFunction[(N, ContextCustom[N, C]), N] = {
      case (n, cc) if p.isDefinedAt(n, cc.c) => p((n, cc.c))._1
    }

    val p2: PartialFunction[(N, C), C] = {
      case (n, c) if p.isDefinedAt((n, c)) => p((n, c))._2
    }

    new Strategy[N, ContextCustom[N, C]](p1).defaultContext(new PartialContextCC[N, C](default, p2)).traverse(t)
  }

  /**
    * Visitor analogous to SlimStrategy just with no new node as return type
    *
    * @param f Function to execute on every node
    * @tparam N Common supertype of every node in the tree
    * @return Visitor object ready to use
    */
  def SlimVisitor[N <: Rewritable](f: N => Unit) = {
    new StrategyVisitor[N, SimpleContext[N]]({ (a: N, _: SimpleContext[N]) => f(a) }) defaultContext new NoContext[N]
  }

  /**
    * Visitor analogous to AncestorStrategy just with no new node as return type
    *
    * @param f Function to execute on every node
    * @tparam N Common supertype of every node in the tree
    * @return Visitor object ready to use
    */
  def AncestorVisitor[N <: Rewritable](f: (N, ContextA[N]) => Unit) = {
    new StrategyVisitor[N, ContextA[N]](f) defaultContext new PartialContextA[N]
  }

  /**
    * Visitor analogous to ContextStrategy just with no new node as return type
    *
    * @param f          Function to execute on every node
    * @param default    Default context value (in case no context is present)
    * @param updateFunc Function that extracts context out of nodes and combines it with existing context
    * @tparam N Common supertype of every node in the tree
    * @tparam C Type of the context
    * @return Visitor object ready to use
    */
  def ContextVisitor[N <: Rewritable, C](f: (N, ContextC[N, C]) => Unit, default: C, updateFunc: PartialFunction[(N, C), C] = PartialFunction.empty) = {
    new StrategyVisitor[N, ContextC[N, C]](f) defaultContext new PartialContextC[N, C](default, updateFunc)
  }
}

/**
  * A class that helps with providing dummy context in a rewriting function. Used to make SlimStrategy compatible with RegexStrategy
  *
  * @param p partial function from node to node
  * @tparam N type of the AST nodes
  */
class AddArtificialContext[N <: Rewritable](p: PartialFunction[N, N]) extends PartialFunction[(N, SimpleContext[N]), N] {
  override def isDefinedAt(x: (N, SimpleContext[N])): Boolean = p.isDefinedAt(x._1)

  override def apply(x: (N, SimpleContext[N])): N = p.apply(x._1)
}

/**
  * Strategy that provides node to node replacement without depending on contexts
  *
  * @param p Partial function from node to node
  * @tparam N Type of the
  */
class SlimStrategy[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag](p: PartialFunction[N, N]) extends Strategy[N, SimpleContext[N]](new AddArtificialContext(p))

// Generic Strategy class. Includes all the required functionality
class Strategy[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, C <: Context[N]](p: PartialFunction[(N, C), N]) extends StrategyInterface[N] {

  // Defines the traversion mode
  protected var traversionMode: Traverse = Traverse.TopDown

  /**
    * Access to the current traversion mode
    *
    * @return Traversion mode
    */
  def getTraversionMode = traversionMode

  /**
    * Define the traversion mode
    *
    * @param t Traversion mode
    * @return Strategy itself (convenience)
    */
  def traverse(t: Traverse): Strategy[N, C] = {
    traversionMode = t
    this
  }

  // Selects the children on which we recurse.
  protected var recursionFunc: PartialFunction[N, Seq[AnyRef]] = PartialFunction.empty

  /**
    * Define the function that specifies the children we recurse on
    *
    * @param r Recursion function
    * @return Strategy itself (convenience)
    */
  def recurseFunc(r: PartialFunction[N, Seq[AnyRef]]): Strategy[N, C] = {
    recursionFunc = r
    this
  }

  // Function to update the context
  protected var upContext: PartialFunction[(N, _), _] = PartialFunction.empty

  protected var defaultContxt: Option[C] = None

  def defaultContext(pC: PartialContext[N, C]): Strategy[N, C] = {
    defaultContxt = Some(pC.get(this))
    this
  }

  // Rule used for rewriting (may be combined from other strategies)
  private var rule: RuleT[N, C] = Rule(p)

  /**
    * Access to the rule used for rewriting
    *
    * @return Rule
    */
  def getRule = rule

  /**
    * Set the rule used for rewriting
    *
    * @param r Rule
    */
  def setRule(r: RuleT[N, C]) = rule = r

  /**
    * Append rule of s to the rule of this. Rule of s will be executed directly after rule of this for every node
    *
    * @param s strategy for combining rules
    * @return strategy with combined rules
    */
  def +(s: Strategy[N, C]): Strategy[N, C] = {
    rule = Append[N, C](rule, s.getRule)
    this
  }

  /**
    * Conditionally append rule of s to the rule of this. Rule of s will be executed directly after rule of this for every node in case rule of this was applied
    *
    * @param s strategy for combining rules
    * @return strategy with combined rules
    */
  def <(s: Strategy[N, C]): Strategy[N, C] = {
    rule = CondAppend[N, C](rule, s.getRule)
    this
  }

  /**
    * First part of the ternary operator in case rule this is applied. apply rule s too
    *
    * @param s strategy for combining rules
    * @return Partial ternary object
    */
  def ?(s: Strategy[N, C]): PartialTernary[N, C] = {
    PartialTernary[N, C](this, s.getRule)
  }

  /**
    * Lift this strategy to an iterative strategy
    *
    * @return iterative strategy
    */
  def repeat: RepeatedStrategy[N] = {
    new RepeatedStrategy[N](this)
  }

  // Select the execution function based on the traversion mode
  protected def selectStrat(node: N, contextUsed: C): N = {
    changed = false
    val result = traversionMode match {
      case Traverse.TopDown => rewriteTopDown(node, contextUsed)
      case Traverse.BottomUp => rewriteBottomUp(node, contextUsed)
      case Traverse.Innermost => rewriteInnermost(node, contextUsed)
    }
    changed = !(result eq node)
    result
  }

  /**
    * Execute the Strategy
    *
    * @param node Root of the AST you want to rewrite
    * @tparam T Type of the rewritten root
    * @return rewritten AST
    */
  override def execute[T <: N](node: N): T = {
    assert(defaultContxt.isDefined, "Default context not set!")
    selectStrat(node, defaultContxt.get).asInstanceOf[T]
  }

  /**
    * Same as simple execute. Allows to define the default context here
    *
    * @param node Root of the AST we want to rewrite
    * @param ctxt Default context for execution
    * @tparam T Type of the rewritten root
    * @return rewritten AST
    */
  def execute[T <: N](node: N, ctxt: PartialContext[N, C]): T = {
    selectStrat(node, ctxt.get(this)).asInstanceOf[T]
  }

  /**
    * Execute the Strategy
    * Same as simple execute just without requiring a type parameter
    * Type of the result node will be the generic type of the AST
    *
    * @param node Root of the AST you want to rewrite
    * @param ctxt Type of the rewritten root
    * @return rewritten AST
    */
  def executeT(node: N, ctxt: PartialContext[N, C]): N = execute[N](node, ctxt)

  def rewriteTopDown[A](node: A, context: C): A = {
    if (noRecursion.contains(node))
      node
    else {
      node match {
        case map: Map[_, _] => map.map(rewriteTopDown(_, context)).asInstanceOf[A]

        case collection: Iterable[_] => collection.map(rewriteTopDown(_, context)).asInstanceOf[A]

        case Some(value) => Some(rewriteTopDown(value, context)).asInstanceOf[A]

        case n: N @unchecked =>
          var c = context.addAncestor(n).asInstanceOf[C]

          val newNode = rule.execute(n, c).getOrElse(n)

          if (noRecursion.contains(newNode))
            newNode.asInstanceOf[A]
          else {
            c = c.update(newNode).asInstanceOf[C]

            val allowedToRecurse = recursionFunc.applyOrElse(newNode, (_: N) => newNode.children).toSet
            val children = newNode.children.map(child => if (allowedToRecurse(child)) rewriteTopDown(child, c) else child)

            (newNode.children = children).asInstanceOf[A]
          }

        case value => value
      }
    }
  }

  def rewriteBottomUp[A](node: A, context: C): A = {
    if (noRecursion.contains(node))
      node
    else {
      node match {
        case map: Map[_, _] => map.map(rewriteBottomUp(_, context)).asInstanceOf[A]

        case collection: Iterable[_] => collection.map(rewriteBottomUp(_, context)).asInstanceOf[A]

        case Some(value) => Some(rewriteBottomUp(value, context)).asInstanceOf[A]

        case n: N @unchecked =>
          val c = context.addAncestor(n).asInstanceOf[C]

          val allowedToRecurse = recursionFunc.applyOrElse(n, (_: N) => n.children).toSet
          val children = n.children.map(child => if (allowedToRecurse(child)) rewriteBottomUp(child, c) else child)

          val newNode = (n.children = children).asInstanceOf[N]

          rule.execute(newNode, c).getOrElse(newNode).asInstanceOf[A]

        case value => value
      }
    }
  }

  def rewriteInnermost[A](node: A, context: C): A = {
    if (noRecursion.contains(node))
      node
    else {
      node match {
        case map: Map[_, _] => map.map(rewriteInnermost(_, context)).asInstanceOf[A]

        case collection: Iterable[_] => collection.map(rewriteInnermost(_, context)).asInstanceOf[A]

        case Some(value) => Some(rewriteInnermost(value, context)).asInstanceOf[A]

        case n: N @unchecked =>
          val c = context.addAncestor(n).asInstanceOf[C]

          val newNode = rule.execute(n, c)

          if (newNode.isDefined)
            newNode.get.asInstanceOf[A]
          else {
            val allowedToRecurse = recursionFunc.applyOrElse(n, (_: N) => n.children).toSet
            val children = n.children.map(child => if (allowedToRecurse(child)) rewriteInnermost(child, c) else child)
            (n.children = children).asInstanceOf[A]
          }

        case value => value
      }
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
class ConcatenatedStrategy[N <: Rewritable](s1: StrategyInterface[N], val s2: StrategyInterface[N]) extends StrategyInterface[N] {
  private var strategies = mutable.ListBuffer.empty[StrategyInterface[N]]

  strategies.append(s1)
  strategies.append(s2)


  override def ||(s: StrategyInterface[N]): ConcatenatedStrategy[N] = {
    strategies.append(s)
    this
  }

  def ||(s: ConcatenatedStrategy[N]): ConcatenatedStrategy[N] = {
    strategies ++= s.strategies
    this
  }

  override def execute[T <: N](node: N): T = strategies.foldLeft(node)((n, strat) => strat.execute[N](n)).asInstanceOf[T]
}

/**
  * This class encapsulates strategies that should be iterative. The execute method allows for execution until fixed point or a fixed number of executions
  *
  * @param s The strategy to iterate
  * @tparam N Type of the AST nodes
  */
class RepeatedStrategy[N <: Rewritable](s: StrategyInterface[N]) extends StrategyInterface[N] {

  /**
    * Execute strategy until fixed point is reached
    *
    * @param node root node of the AST
    * @tparam T type of the rewritten root
    * @return rewritten root
    */
  override def execute[T <: N](node: N): T = {
    val result: T = s.execute[T](node)
    if (!s.hasChanged) {
      result
    } else {
      execute[T](result)
    }
  }

  /**
    * Execute strategy a fixed number of times
    *
    * @param node root node of the AST
    * @param i    number of iterations
    * @tparam T Type of the result node
    * @return rewritten root
    */
  def execute[T <: N](node: N, i: Int): N = {
    if (i <= 0) {
      node
    }
    else {
      val result = s.execute[T](node)
      if (s.hasChanged) {
        result
      } else {
        execute[T](result, i - 1)
      }
    }
  }

  override def hasChanged: Boolean = s.hasChanged
}

/**
  * Base trait for all Strategy contexts
  *
  * @tparam N Common supertype of every node in the tree
  */
trait Context[N <: Rewritable] {
  protected def transformer: StrategyInterface[N]

  /**
    * Shortcut to define nodes that should not be recursed on
    *
    * @param node node to prevent recursion on
    * @tparam T type of the node
    * @return return the node again (convenience)
    */
  def noRec[T <: N](node: Rewritable): T = {
    transformer.noRec[T](node)
  }

  /**
    * Get access to the transformer object itself
    *
    * @return the current transformer
    */
  def getTransformer: StrategyInterface[N] = transformer

  // Add an ancestor to the context
  private[rewriter] def addAncestor(node: N): Context[N]

  // Replace the current node with a new one
  private[rewriter] def replaceNode(node: N): Context[N]

  // Update the context
  private[rewriter] def update(node: N): Context[N]
}

/**
  * Encapsulates context information without ancestors or custom context
  *
  * @param transformer current transformer
  * @tparam N Common supertype of every node in the tree
  */
class SimpleContext[N <: Rewritable](protected val transformer: StrategyInterface[N]) extends Context[N] {
  override def addAncestor(node: N): SimpleContext[N] = this

  override def replaceNode(node: N): SimpleContext[N] = this

  override def update(node: N): SimpleContext[N] = this
}

/**
  * Encapsulates context information with ancestors but no custom context
  *
  * @param ancestorList List of ancestors
  * @param transformer  current transformer
  * @tparam N Common supertype of every node in the tree
  */
class ContextA[N <: Rewritable](val ancestorList: Seq[N], protected val transformer: StrategyInterface[N]) extends Context[N] {

  // Add an ancestor to the context
  override def addAncestor(n: N): ContextA[N] = {
    new ContextA[N](ancestorList ++ Seq(n), transformer)
  }

  // Replace the current node with a new one
  override def replaceNode(n: N): ContextA[N] = {
    new ContextA[N](ancestorList.dropRight(1) ++ Seq(n), transformer)
  }

  // Update the context
  override def update(n: N): ContextA[N] = {
    replaceNode(n)
  }

  /**
    * Current node
    */
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

  lazy val family: Seq[Any] = {
    parent match {
      case viper.silver.ast.Seqn(stmts, _) => stmts
      case viper.silver.ast.FuncApp(_, args) => args
      case _ => parent.children
    }
  }

  /** Parent of node.
    * Will result in a `java.util.NoSuchElementException` if no parent is available.
    */
  lazy val parent: N = {
    assert(ancestorList.length > 1, "No parent information available in context")
    ancestorList.dropRight(1).last
  }

  /** Parent of node, if available. */
  lazy val parentOption: Option[N] = ancestorList.dropRight(1).lastOption

  // Equality between nodes
  private def isEqualNode(elem: Any): Boolean = elem match {
    case p: AnyRef => p eq node
    case _ => node == elem
  }

}

/**
  * Encapsulates context information with ancestors and custom context
  *
  * @param aList       List of ancestors
  * @param c           custom context object
  * @param transformer current transformer
  * @param upContext   Function to update the context
  * @tparam N      Common supertype of every node in the tree
  * @tparam CUSTOM Type of custom context
  */
class ContextC[N <: Rewritable, CUSTOM](aList: Seq[N], val c: CUSTOM, transformer: StrategyInterface[N], upContext: PartialFunction[(N, CUSTOM), CUSTOM]) extends ContextA[N](aList, transformer) {

  // Add an ancestor to the context
  override def addAncestor(n: N): ContextC[N, CUSTOM] = {
    new ContextC(ancestorList ++ Seq(n), c, transformer, upContext)
  }

  // Replace the current node with a new one
  override def replaceNode(n: N): ContextC[N, CUSTOM] = {
    new ContextC(ancestorList.dropRight(1) ++ Seq(n), c, transformer, upContext)
  }

  // Perform the custom update part of the update
  def updateCustom(n: N): ContextC[N, CUSTOM] = {
    val cust = upContext.applyOrElse((n, c), (els:(N, CUSTOM)) => els._2)
    new ContextC[N, CUSTOM](ancestorList, cust, transformer, upContext)
  }

  // Update the context with node and custom context
  override def update(n: N): ContextC[N, CUSTOM] = {
    replaceNode(n).updateCustom(node)
  }
}

/**
  * Encapsulates context information with custom context and *no* ancestors
  *
  * @param c           custom context object
  * @param transformer current transformer
  * @param upContext   Function to update the context
  * @tparam N      Common supertype of every node in the tree
  * @tparam CUSTOM Type of custom context
  */
class ContextCustom[N <: Rewritable, CUSTOM](val c: CUSTOM, override protected val transformer: StrategyInterface[N], private val upContext: PartialFunction[(N, CUSTOM), CUSTOM]) extends SimpleContext[N](transformer) {

  // Perform the custom update part of the update
  def updateCustom(n: N): ContextCustom[N, CUSTOM] = {
    val updated = upContext.applyOrElse((n, c), (els:(N, CUSTOM)) => els._2)
    new ContextCustom[N, CUSTOM](updated, transformer, upContext)
  }

  // Update the context with node and custom context
  override def update(n: N): ContextCustom[N, CUSTOM] = {
    updateCustom(n)
  }
}

/**
  * Context object that does not contain all information yet. Provides functions to lift the object into a full context
  *
  * @tparam N Common supertype of every node in the tree
  * @tparam C Type of context
  */
trait PartialContext[N <: Rewritable, C <: Context[N]] {

  /**
    * Provide the transformer for the real context
    *
    * @param transformer current transformer
    * @return A complete Context object
    */
  def get(transformer: StrategyInterface[N]): C
}

/**
  * Partial context for SimpleContext.
  *
  * @tparam N Common supertype of every node in the tree
  */
class NoContext[N <: Rewritable] extends PartialContext[N, SimpleContext[N]] {
  /**
    * Provide the transformer for the real context
    *
    * @param transformer current transformer
    * @return A complete SimpleContext object
    */
  override def get(transformer: StrategyInterface[N]): SimpleContext[N] = new SimpleContext[N](transformer)
}

/**
  * Partial context for ContextA
  *
  * @param aList List of ancestors
  * @tparam N Common supertype of every node in the tree
  */
class PartialContextA[N <: Rewritable](val aList: Seq[N] = Seq()) extends PartialContext[N, ContextA[N]] {

  /**
    * Provide the transformer for the real context
    *
    * @param transformer current transformer
    * @return A complete ContextA object
    */
  override def get(transformer: StrategyInterface[N]): ContextA[N] = new ContextA[N](aList, transformer)
}

/**
  * Partial context for ContextC
  *
  * @param custom    Custom context object
  * @param upContext Function to update the context
  * @param aList     List of ancestors
  * @tparam N      Common supertype of every node in the tree
  * @tparam CUSTOM Type of custom context
  */
class PartialContextC[N <: Rewritable, CUSTOM](val custom: CUSTOM, val upContext: PartialFunction[(N, CUSTOM), CUSTOM] = PartialFunction.empty, val aList: Seq[N] = Seq()) extends PartialContext[N, ContextC[N, CUSTOM]] {

  /**
    * Provide information to complete ContextC object
    *
    * @param list        List of ancestors
    * @param upC         Update function for custom context
    * @param transformer Current transformer
    * @return A complete ContextC object
    */
  def get(list: Seq[N], upC: PartialFunction[(N, CUSTOM), CUSTOM], transformer: StrategyInterface[N]): ContextC[N, CUSTOM] = new ContextC[N, CUSTOM](list, custom, transformer, upC)

  /**
    * Provide information to complete ContextC object
    *
    * @param list        List of ancestors
    * @param transformer Current transformer
    * @return A complette ContextC object
    */
  def get(list: Seq[N], transformer: StrategyInterface[N]): ContextC[N, CUSTOM] = get(list, upContext, transformer)

  /**
    * Provide the transformer for the real context
    *
    * @param transformer current transformer
    * @return A complete ContextC object
    */
  override def get(transformer: StrategyInterface[N]): ContextC[N, CUSTOM] = get(aList, transformer)
}

/**
  * Partial context for ContextCustom
  *
  * @param custom    Custom context object
  * @param upContext Function to update the context
  * @tparam N      Common supertype of every node in the tree
  * @tparam CUSTOM Type of custom context
  */
class PartialContextCC[N <: Rewritable, CUSTOM](val custom: CUSTOM, val upContext: PartialFunction[(N, CUSTOM), CUSTOM] = PartialFunction.empty) extends PartialContext[N, ContextCustom[N, CUSTOM]] {

  /**
    * Provide information to complete ContextCustom object
    *
    * @param upC         Update function for custom context
    * @param transformer Current transformer
    * @return A complete ContextC object
    */
  def get(upC: PartialFunction[(N, CUSTOM), CUSTOM], transformer: StrategyInterface[N]): ContextCustom[N, CUSTOM] = new ContextCustom[N, CUSTOM](custom, transformer, upC)

  /**
    * Provide the transformer for the real context
    *
    * @param transformer current transformer
    * @return A complete ContextC object
    */
  override def get(transformer: StrategyInterface[N]): ContextCustom[N, CUSTOM] = get(upContext, transformer)
}



/**
  * A visitor that executes a unit-result function on every node
  *
  * @param visitNode Function used for visiting every node
  * @tparam N Type of the AST nodes
  * @tparam C Type of context
  */
class StrategyVisitor[N <: Rewritable, C <: Context[N]](val visitNode: (N, C) => Unit) extends StrategyInterface[N] {

  // Function that defines recursion
  protected var recursionFunc: PartialFunction[N, Seq[AnyRef]] = PartialFunction.empty

  /**
    * Define the recursion function
    *
    * @param r recursion function
    * @return Visitor
    */
  def recurseFunc(r: PartialFunction[N, Seq[AnyRef]]): StrategyVisitor[N, C] = {
    recursionFunc = r
    this
  }

  // Default context
  protected var defaultContxt: Option[C] = None

  /**
    * Define the default context
    *
    * @param pC Partial context (transformer will be filled in)
    * @return visitor itself (convenience)
    */
  def defaultContext(pC: PartialContext[N, C]): StrategyVisitor[N, C] = {
    defaultContxt = Some(pC.get(this))
    this
  }

  /**
    * Execute the visitor on an object (execute to allow compatibility with other rewriting strategies)
    *
    * @param node root node of the AST
    * @tparam T type of the rewritten root
    * @return rewritten root
    */
  override def execute[T <: N](node: N): T = {
    assert(defaultContxt.isDefined, "Default context not set!")
    visitTopDown(node, defaultContxt.get)
    node.asInstanceOf[T]
  }

  /**
    * Visit the AST  at the root node. Basically execute with no return value
    *
    * @param node root node of the AST
    */
  def visit(node: N): Unit = {
    execute[N](node)
  }

  // Method used for visiting
  private def visitTopDown[A](node: A, context: C): Unit = {
    if (!noRecursion.contains(node)) {
      node match {
        case map: Map[_, _] => map.map(visitTopDown(_, context))

        case collection: Iterable[_] => collection.map(visitTopDown(_, context))

        case Some(value) => Some(visitTopDown(value, context))

        case n: N @unchecked =>
          var c = context.addAncestor(n).asInstanceOf[C]

          visitNode(n, c)

          c = c.update(n).asInstanceOf[C]

          val allowedToRecurse = recursionFunc.applyOrElse(n, (_: N) => n.children).toSet
          n.children.filter(allowedToRecurse).foreach(visitTopDown(_, c))

        case _ =>
      }
    }
  }
}

/**
  * Query a Tree for useful information
  *
  * @param getInfo Extractor used to get information from a node
  * @tparam N Type of the AST nodes
  * @tparam B Result type of the Query
  */
class Query[N <: Rewritable, B](val getInfo: PartialFunction[N, B]) {

  // Function used to combine results together
  protected var accumulator: Seq[B] => B = (x: Seq[B]) => x.head

  /**
    * Acces the accumulator function
    *
    * @return The accumulator function
    */
  def getAccumulator = accumulator

  /**
    * Define the accumulator that combines the results of all children together into one
    *
    * @param a Accumulator function
    * @return Query itself (convenience)
    */
  def accumulate(a: Seq[B] => B): Query[N, B] = {
    accumulator = a
    this
  }

  // Default Query element
  protected var nElement: Option[B] = None

  /**
    * Access the neutral element
    *
    * @return Neutral element
    */
  def getNeutralElement = nElement

  /**
    * Define the default value for the query result (like the default value in fold)
    *
    * @param ne Neutral element
    * @return Query itself (convenience)
    */
  def neutralElement(ne: B): Query[N, B] = {
    nElement = Some(ne)
    this
  }

  // Function that defines the recursion
  protected var recursionFunc: PartialFunction[N, Seq[AnyRef]] = PartialFunction.empty

  def recurseFunc(r: PartialFunction[N, Seq[AnyRef]]): Query[N, B] = {
    recursionFunc = r
    this
  }

  /**
    * Execute the Query
    *
    * @param node Root of the AST
    * @return Query result
    */

  def execute[A](node: A): B = {
    node match {
      case map: Map[_, _] => accumulator(map.map(execute(_)).toSeq)

      case collection: Iterable[_] => accumulator(collection.map(execute).toSeq)

      case Some(value) => execute(value)

      case n: N @unchecked =>
        // Query current node
        val nodeQueryRes = getInfo.applyOrElse(n, (n: N) => {
          assert(nElement.isDefined, "Node " + n + "does not define a result. Either define it in query or specify neutral element")
          nElement.get
        })

        val allowedToRecurse = recursionFunc.applyOrElse(n, (_: N) => n.children).toSet
        val childrenQueryRes = accumulator(n.children.filter(allowedToRecurse).map(execute))

        accumulator(Seq(nodeQueryRes, childrenQueryRes))

      case _ => accumulator(Seq())
    }
  }
}


/**
  * A trait that is used for providing an interface for rules and rule combinators
  */
private[utility] trait RuleT[N <: Rewritable, C <: Context[N]] {
  def execute(node: N, context: C): Option[N]
}

/**
  * Rule lifts a partial function to a rule that is used in Strategy
  *
  * @param r The partial function
  */
private case class Rule[N <: Rewritable, C <: Context[N]](r: PartialFunction[(N, C), N]) extends RuleT[N, C] {
  override def execute(node: N, context: C): Option[N] = {
    val res = r.applyOrElse((node, context), (els:(N, C)) => els._1)
    if (node eq res) {
      None
    } else {
      Some(res)
    }
  }
}

/**
  * Class Append takes two rules and executes them one after another
  *
  * @param r1 First rule
  * @param r2 Second rule
  */
private case class Append[N <: Rewritable, C <: Context[N]](r1: RuleT[N, C], r2: RuleT[N, C]) extends RuleT[N, C] {

  override def execute(node: N, context: C): Option[N] = {
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
private case class CondAppend[N <: Rewritable, C <: Context[N]](r1: RuleT[N, C], r2: RuleT[N, C]) extends RuleT[N, C] {

  override def execute(node: N, context: C): Option[N] = {
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
private case class Ternary[N <: Rewritable, C <: Context[N]](r1: RuleT[N, C], r2: RuleT[N, C], r3: RuleT[N, C]) extends RuleT[N, C] {

  override def execute(node: N, context: C): Option[N] = {
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

/**
  * Helper class to allow the construction of the ternary construct. We already specified S1 and S2 from: S1 ? S2 : S3 and need S3
  *
  * @param s  the base strategy S1
  * @param r2 rule of strategy S2
  * @tparam N type of all AST nodes
  * @tparam C type of context
  */
case class PartialTernary[N <: Rewritable, C <: Context[N]](s: Strategy[N, C], r2: RuleT[N, C]) {
  def |(s2: Strategy[N, C]): Strategy[N, C] = {
    s.setRule(Ternary(s.getRule, r2, s2.getRule))
    s
  }
}