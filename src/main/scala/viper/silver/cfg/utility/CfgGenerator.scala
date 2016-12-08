/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.cfg.utility

import viper.silver.ast._
import viper.silver.cfg._

import scala.collection.mutable

/**
  * An object that provides the translation from an AST into the corresponding
  * CFG.
  *
  * The generation proceeds in four phases:
  *
  * 1. In a first phase, the AST is transformed into a list of temporary
  * statements. The control flow is modeled with additional (conditional) jump
  * statements.
  */
object CfgGenerator {
  type SilverCfg = Cfg[Stmt, Exp]
  type SilverBlock = viper.silver.cfg.Block[Stmt, Exp]
  type SilverEdge = viper.silver.cfg.Edge[Stmt, Exp]

  /**
    * Returns a CFG corresponding to the given method.
    *
    * @param method The method.
    * @return The corresponding CFG.
    */
  def toCfg(method: Method): SilverCfg = {
    // generate cfg for the body
    val bodyCfg = method.body.toCfg

    // create blocks and corresponding edges for pre and postconditions
    val preBlock: SilverBlock = PreconditionBlock(method.pres)
    val postBlock: SilverBlock = PostconditionBlock(method.posts)
    val preEdge: SilverEdge = UnconditionalEdge(preBlock, bodyCfg.entry, Kind.Normal)
    val postEdge: SilverEdge = UnconditionalEdge(bodyCfg.exit, postBlock, Kind.Normal)

    // create cfg with pre and postconditions
    val blocks = preBlock :: postBlock :: bodyCfg.blocks.toList
    val edges = preEdge :: postEdge :: bodyCfg.edges.toList
    Cfg(blocks, edges, preBlock, postBlock)
  }

  /**
    * Returns a CFG corresponding to the given AST node.
    *
    * @param ast The AST node.
    * @return The corresponding CFG.
    */
  def toCfg(ast: Stmt): SilverCfg = {
    val phase1 = new Phase1(ast)
    val phase2 = new Phase2(phase1)
    val (loops, parents) = phase2.loopInfo
    LoopDetector.detect(phase2.cfg, loops, parents)
  }

  /**
    * A label that represents the target of a jump.
    *
    * @param name The name of the label.
    */
  case class TmpLabel(name: String)

  object TmpLabel {
    var id = 0

    def generate(name: String): TmpLabel = {
      id = id + 1
      new TmpLabel(s"${name}_$id")
    }
  }

  /**
    * An temporary statement that is used during the translation of an AST to a
    * CFG.
    */
  sealed trait TmpStmt {
  }

  final case class WrappedStmt(stmt: Stmt)
    extends TmpStmt

  final case class JumpStmt(target: TmpLabel)
    extends TmpStmt

  final case class ConditionalJumpStmt(cond: Exp, thnTarget: TmpLabel, elsTarget: TmpLabel)
    extends TmpStmt

  final case class LoopHeadStmt(invs: Seq[Exp], after: TmpLabel)
    extends TmpStmt

  final case class ConstrainingStmt(vars: Seq[LocalVar], body: SilverCfg, after: TmpLabel)
    extends TmpStmt

  final case class EmptyStmt()
    extends TmpStmt

  /**
    * The first phase of the generation of the CFG that transforms the AST into
    * a list of temporary statements.
    */
  class Phase1(ast: Stmt) {
    /**
      * The map used to look up the index of a label in the list of temporary
      * statements.
      */
    val labels: mutable.Map[TmpLabel, Int] = mutable.Map()

    /**
      * The list of temporary statements.
      */
    val stmts: mutable.ListBuffer[TmpStmt] = mutable.ListBuffer()

    addStatement(EmptyStmt())
    run(ast)

    /**
      * Recursively transforms the given AST node into a list of temporary
      * statements.
      *
      * @param stmt The AST node to transform.
      */
    private def run(stmt: Stmt): Unit = stmt match {
      case If(cond, thn, els) =>
        // create labels
        val thnTarget = TmpLabel.generate("then")
        val elsTarget = TmpLabel.generate("else")
        val afterTarget = TmpLabel.generate("after")
        // conditional jump to then/else branch
        addStatement(ConditionalJumpStmt(cond, thnTarget, elsTarget))
        // process then branch
        addLabel(thnTarget)
        run(thn)
        addStatement(JumpStmt(afterTarget))
        // process else branch
        addLabel(elsTarget)
        run(els)
        addStatement(JumpStmt(afterTarget))
        // set label after if statement
        addLabel(afterTarget)
      case While(cond, invs, locals, body) =>
        // create labels
        val headTarget = TmpLabel.generate("head")
        val loopTarget = TmpLabel.generate("loop")
        val afterTarget = TmpLabel.generate("after")
        // process loop head
        addLabel(headTarget, addEmptyStmt = false)
        addStatement(LoopHeadStmt(invs, afterTarget))
        addStatement(ConditionalJumpStmt(cond, loopTarget, afterTarget))
        // process loop body
        // TODO: Do we have to process the locals here?
        addLabel(loopTarget)
        run(body)
        addStatement(JumpStmt(headTarget))
        // set label after loop
        addLabel(afterTarget)
      case Constraining(vars, body) =>
        val after = TmpLabel.generate("after")
        val cfg = toCfg(body)
        addStatement(ConstrainingStmt(vars, cfg, after))
        addLabel(after)
      case Seqn(stmts) =>
        stmts.foreach(run)
      case Goto(name) =>
        val target = TmpLabel(name)
        addStatement(JumpStmt(target))
      case Label(name, invs) =>
        // TODO: Handle invariants.
        val label = TmpLabel(name)
        addLabel(label)
      case _: LocalVarAssign |
           _: FieldAssign |
           _: Inhale |
           _: Exhale |
           _: Fold |
           _: Unfold |
           _: Package |
           _: Apply |
           _: MethodCall |
           _: Fresh |
           _: NewStmt |
           _: Assert =>
        // handle regular, non-control statements
        addStatement(WrappedStmt(stmt))
    }

    /**
      * Adds the given label and maps it to the next index in the list of
      * statements. Also, an empty statement is added to make sure that the
      * label maps to a valid index, unless the corresponding flag is false.
      *
      * @param label        The label to add.
      * @param addEmptyStmt Flag indicating whether an empty statement should be
      *                     added.
      */
    private def addLabel(label: TmpLabel, addEmptyStmt: Boolean = true) = {
      val index = stmts.size
      labels.put(label, index)
      if (addEmptyStmt) addStatement(EmptyStmt())
    }

    /**
      * Adds the given statement to the list of statements.
      *
      * @param stmt The statement to add.
      */
    private def addStatement(stmt: TmpStmt): Unit =
      stmts.append(stmt)
  }

  /**
    * A temporary edge used during the construction of the control flow graph.
    *
    * The source and target are specified with respect to the index of the
    * temporary statement in the list of statements that corresponds to the
    * basic block at the source or the target, respectively, of the edge.
    */
  sealed trait TmpEdge {
    def source: Int
    def target: Int
  }

  final case class TmpUnconditionalEdge(source: Int, target: Int)
    extends TmpEdge

  final case class TmpConditionalEdge(cond: Exp, source: Int, target: Int)
    extends TmpEdge

  class Phase2(phase1: Phase1) {
    /**
      * A map mapping from indices of the list of statements (of the first
      * phase) that are at the top of a basic block to their corresponding basic
      * block.
      */
    private val blocks: mutable.Map[Int, SilverBlock] = mutable.Map()

    /**
      * The list of edges.
      */
    private val edges: mutable.ListBuffer[SilverEdge] = mutable.ListBuffer()

    /**
      * The entry block of the control flow graph. The value is computed lazily
      * and therefore should not be accessed before all blocks are added.
      */
    private lazy val entry = blocks.get(0).get

    /**
      * The exit block of the control flow graph. The value is computed lazily
      * and therefore should not be accessed before all blocks are added.
      */
    private lazy val exit = blocks.get(current).get

    /**
      * The list buffer used to accumulate the statements of the current block.
      */
    private val tmpStmts: mutable.ListBuffer[Stmt] = mutable.ListBuffer()

    /**
      * The list buffer used to accumulate the temporary edges.
      */
    private val tmpEdges: mutable.ListBuffer[TmpEdge] = mutable.ListBuffer()


    /**
      * The stack used to keep track of the loops. The stack stores tuples where
      * the first entry is the id of the basic block at the head of the loop and
      * the second entry is the index in the list of statements right after the
      * last statement that syntactically belongs to the loop. The second entry
      * is used to lazily remove the tuples from the stack.
      */
    private val loopStack: mutable.Stack[(Int, Int)] = mutable.Stack()

    /**
      * The index of the current block.
      */
    private var current = 0

    /**
      * The map mapping the ids of basic blocks of a loop to the id of the basic
      * block at the head of that loop.
      */
    private val loops: mutable.Map[Int, Int] = mutable.Map()

    /**
      * The map mapping the ids of basic blocks at the head of a loop to the id
      * of the basic block that is at head of the parent loop.
      */
    private val parents: mutable.Map[Int, Int] = mutable.Map()

    run()

    /**
      * The cfg.
      */
    lazy val cfg: SilverCfg = Cfg(blocks.values.toList, edges.toList, entry, exit)

    /**
      * The loop information used for constructing in and out edges.
      */
    lazy val loopInfo: (Map[Int, Int], Map[Int, Int]) =  (loops.toMap, parents.toMap)

    private def run(): Unit = {

      addBlock(current, StatementBlock())

      for ((stmt, index) <- phase1.stmts.zipWithIndex) {
        if (!stmt.isInstanceOf[WrappedStmt] && tmpStmts.nonEmpty) {
          finalizeBlock()
        }

        stmt match {
          case WrappedStmt(s) =>
            tmpStmts.append(s)
          case JumpStmt(target) =>
            addTmpEdge(TmpUnconditionalEdge(current, resolve(target)))
          case ConditionalJumpStmt(cond, thnTarget, elsTarget) =>
            val neg = Not(cond)(cond.pos)
            addTmpEdge(TmpConditionalEdge(cond, current, resolve(thnTarget)))
            addTmpEdge(TmpConditionalEdge(neg, current, resolve(elsTarget)))
          case LoopHeadStmt(invs, after) =>
            val last = current
            current = index

            val block: SilverBlock = LoopHeadBlock(invs, Nil)

            // set loop parent information
            head().foreach(old => parents.put(block.id, old))
            // push current loop id block onto stack
            loopStack.push((block.id, resolve(after)))

            addBlock(current, block)
            addTmpEdge(TmpUnconditionalEdge(last, current))
          case ConstrainingStmt(vars, body, after) =>
            val last = current
            current = index
            addBlock(current, ConstrainingBlock(vars, body))
            addTmpEdge(TmpUnconditionalEdge(last, current))
            addTmpEdge(TmpUnconditionalEdge(current, resolve(after)))
          case EmptyStmt() =>
            current = index
            addBlock(current, StatementBlock())
        }
      }

      if (tmpStmts.nonEmpty) finalizeBlock()

      tmpEdges.map(finalizeEdge).foreach(addEdge)
    }

    private def resolve(label: TmpLabel): Int =
      phase1.labels.get(label).get

    private def head(): Option[Int] = {
      // lazily pop loops that we left
      while(loopStack.headOption.exists(_._2 <= current)) loopStack.pop()
      // return id of the current loop head
      loopStack.headOption.map(_._1)
    }

    private def addBlock(index: Int, block: SilverBlock) = {
      // set loop information
      head().foreach(head => loops.put(block.id, head))
      blocks.put(index, block)
    }

    private def addEdge(edge: SilverEdge) =
      edges.append(edge)

    private def addTmpEdge(edge: TmpEdge) = {
      tmpEdges.append(edge)
      if (!blocks.contains(edge.target)) blocks.put(edge.target, StatementBlock())
    }

    private def finalizeBlock() = {
      val stmts = tmpStmts.toList
      tmpStmts.clear()
      addBlock(current, StatementBlock(stmts))
    }

    private def finalizeEdge(edge: TmpEdge): SilverEdge = {
      val source = blocks.get(edge.source).get
      val target = blocks.get(edge.target).get
      edge match {
        case TmpUnconditionalEdge(_, _) => UnconditionalEdge(source, target)
        case TmpConditionalEdge(cond, _, _) => ConditionalEdge(cond, source, target)
      }
    }
  }
}