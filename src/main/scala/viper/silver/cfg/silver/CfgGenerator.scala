// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg.silver

import viper.silver.ast._
import viper.silver.cfg._
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.cfg.utility.{CfgSimplifier, LoopDetector}
import java.util.concurrent.atomic.AtomicInteger

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
  *
  * 2. In a second phase, the list of statements is transformed into a control
  * flow graph.
  *
  * 3. In a third phase, the loops are detected and edges entering and leaving
  * the loops are marked as in and out edges.
  *
  * 4. In a fourth phase, the control flow graph is simplified by removing some
  * degeneracies such as empty basic block with only one ingoing and outgoing
  * edge.
  */
object CfgGenerator {
  /**
    * Returns a CFG corresponding to the given method.
    *
    * @param method The method.
    * @return The corresponding CFG.
    */
  def methodToCfg(method: Method, simplify: Boolean = true): SilverCfg = {
    // generate cfg for the body
    val bodyCfg =
      method.body.getOrElse(Seqn(Vector.empty, Vector.empty)())
                 .toCfg(simplify = false)

    // create precondition block and corresponding edge
    val preBlock: SilverBlock = PreconditionBlock(method.pres)
    val preEdge: SilverEdge = UnconditionalEdge(preBlock, bodyCfg.entry, Kind.Normal)

    // create cfg
    val cfg = bodyCfg.exit match {
      case Some(exit) =>
        // create postcondition block and corresponding edge
        val postBlock: SilverBlock = PostconditionBlock(method.posts)
        val postEdge: SilverEdge = UnconditionalEdge(exit, postBlock, Kind.Normal)
        // create cfg with pre- and postconditions and local variables
        val blocks = preBlock :: postBlock :: bodyCfg.blocks.toList
        val edges = preEdge :: postEdge :: bodyCfg.edges.toList
        SilverCfg(blocks, edges, preBlock, Some(postBlock))
      case None =>
        // create cfg with preconditions and local variables but no postconditions
        val blocks = preBlock :: bodyCfg.blocks.toList
        val edges = preEdge :: bodyCfg.edges.toList
        SilverCfg(blocks, edges, preBlock, None)
    }

    if (simplify) CfgSimplifier.simplify[SilverCfg, Stmt, Exp](cfg)
    else cfg
  }

  /**
    * Returns a CFG corresponding to the given AST node.
    *
    * @param ast The AST node.
    * @return The corresponding CFG.
    */
  def statementToCfg(ast: Stmt, simplify: Boolean = true): SilverCfg = {
    val phase1 = new Phase1(ast)
    val phase2 = new Phase2(phase1)

    val cfg = phase2.cfg
    val pruned = CfgSimplifier.pruneUnreachable[SilverCfg, Stmt, Exp](cfg)
    val detected = LoopDetector.detect[SilverCfg, Stmt, Exp](pruned, phase2.loops)

    if (simplify) CfgSimplifier.simplify[SilverCfg, Stmt, Exp](detected)
    else detected
  }

  /**
    * A label that represents the target of a jump.
    *
    * @param name The name of the label.
    */
  case class TmpLabel(name: String)

  object TmpLabel {
    var id = new AtomicInteger(0)

    def generate(name: String): TmpLabel = {
      val freshId = id.incrementAndGet()
      new TmpLabel(s"${freshId}_${name}")
    }
  }

  /**
    * An temporary statement that is used during the translation of an AST to a
    * CFG.
    */
  sealed trait TmpStmt

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
      case While(cond, invs, body) =>
        // create labels
        val headTarget = TmpLabel.generate("head")
        val loopTarget = TmpLabel.generate("loop")
        val afterTarget = TmpLabel.generate("after")
        // process loop head
        addLabel(headTarget, addEmptyStmt = false)
        addStatement(LoopHeadStmt(invs, afterTarget))
        addStatement(ConditionalJumpStmt(cond, loopTarget, afterTarget))
        // process loop body
        addLabel(loopTarget)
        run(body)
        addStatement(JumpStmt(headTarget))
        // set label after loop
        addLabel(afterTarget)
      case Constraining(vars, body) =>
        val after = TmpLabel.generate("after")
        val cfg = statementToCfg(body)
        addStatement(ConstrainingStmt(vars, cfg, after))
        addLabel(after)
      case Seqn(ss, scopedDecls) =>
        val locals = scopedDecls.collect {case l: LocalVarDecl => l}
        for (local <- locals) {
          val decl = LocalVarDeclStmt(local)(pos = local.pos)
          addStatement(WrappedStmt(decl))
        }
        ss.foreach(run)
      case Goto(name) =>
        val target = TmpLabel(name)
        addStatement(JumpStmt(target))
      case Label(name, invs) =>
        val label = TmpLabel(name)
        addLabel(label)
        addStatement(WrappedStmt(stmt))
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
           _: Assert |
           _: LocalVarDeclStmt |
           _: Assume =>
        // handle regular, non-control statements
        addStatement(WrappedStmt(stmt))
      case _: ExtensionStmt => sys.error("Extension statements are not handled.")
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

  case class TmpUnconditionalEdge(source: Int, target: Int)
    extends TmpEdge

  case class TmpConditionalEdge(cond: Exp, source: Int, target: Int)
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
    private lazy val entry: SilverBlock = blocks.get(0).get

    /**
      * The exit block of the control flow graph. The value is computed lazily
      * and therefore should not be accessed before all blocks are added.
      */
    private lazy val exit: SilverBlock = current.flatMap(blocks.get).getOrElse(StatementBlock())

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
      * the first entry is the basic block at the head of the loop and the
      * second entry is the index in the list of statements right after the last
      * statement that syntactically belongs to the loop. The second entry is
      * used to lazily remove the tuples from the stack.
      */
    private var loopStack = List.empty[(SilverBlock, Int)]

    /**
      * The index of the current block. The index is optional since there might
      * be no current block (e.g. after a jump).
      */
    private var current: Option[Int] = None

    /**
      * The map mapping the blocks to the set of loop heads of all loops the
      * block belongs to.
      */
    private val _loops: mutable.Map[SilverBlock, Set[SilverBlock]] = mutable.Map()

    run()

    /**
      * The cfg.
      */
    lazy val cfg: SilverCfg = SilverCfg(blocks.values.toList, edges.toList, entry, Some(exit))

    /**
      * The loop information used for constructing in and out edges.
      */
    lazy val loops: Map[SilverBlock, Set[SilverBlock]] = _loops.toMap

    private def run(): Unit = {
      for ((stmt, index) <- phase1.stmts.zipWithIndex) {
        if (!stmt.isInstanceOf[WrappedStmt] && tmpStmts.nonEmpty) {
          finalizeBlock()
        }

        stmt match {
          case WrappedStmt(s) =>
            tmpStmts.append(s)
          case JumpStmt(target) =>
            current.foreach { currentIndex =>
              addTmpEdge(TmpUnconditionalEdge(currentIndex, resolve(target)))
            }
            current = None
          case ConditionalJumpStmt(cond, thnTarget, elsTarget) =>
            current.foreach { currentIndex =>
              val neg = Not(cond)(cond.pos)
              addTmpEdge(TmpConditionalEdge(cond, currentIndex, resolve(thnTarget)))
              addTmpEdge(TmpConditionalEdge(neg, currentIndex, resolve(elsTarget)))
            }
            current = None
          case LoopHeadStmt(invs, after) =>
            current.foreach { last =>
              current = Some(index)
              // create loop head
              val block: SilverBlock = LoopHeadBlock(invs, Nil)
              // push current loop id block onto stack
              loopStack = (block, resolve(after)) :: loopStack
              // add loop head
              addBlock(index, block)
              addTmpEdge(TmpUnconditionalEdge(last, index))
            }
          case ConstrainingStmt(vars, body, after) =>
            current.foreach { last =>
              current = Some(index)
              addBlock(index, ConstrainingBlock(vars, body))
              addTmpEdge(TmpUnconditionalEdge(last, index))
              addTmpEdge(TmpUnconditionalEdge(index, resolve(after)))
            }
          case EmptyStmt() =>
            current.foreach { last =>
              addTmpEdge(TmpUnconditionalEdge(last, index))
            }

            current = Some(index)
            addBlock(index, StatementBlock())
        }
      }

      if (tmpStmts.nonEmpty) finalizeBlock()

      tmpEdges.map(finalizeEdge).foreach(addEdge)
    }

    private def resolve(label: TmpLabel): Int =
      phase1.labels.get(label) match {
        case Some(n) => n
        case None =>
          sys.error(s"Cannot resolve label '${label.name}', probably because it is out of scope. "
            + "This happens, e.g. when jumping out of a constraining-block.")
      }

    private def heads(index: Int): Set[SilverBlock] = {
      // lazily pop loops that we left
      while (loopStack.headOption.exists(_._2 <= index)) loopStack = loopStack.tail
      // return id of the current loop head
      loopStack.map(_._1).toSet
    }

    private def addBlock(index: Int, block: SilverBlock) = {
      // set loop information
      _loops.put(block, heads(index))
      blocks.put(index, block)
    }

    private def addEdge(edge: SilverEdge) =
      edges.append(edge)

    private def addTmpEdge(edge: TmpEdge) = {
      tmpEdges.append(edge)
      if (!blocks.contains(edge.target)) blocks.put(edge.target, StatementBlock())
    }

    private def finalizeBlock() = {
      current.foreach { index =>
        val block: SilverBlock = tmpStmts.toList match {
          case (l@Label(_, invs)) :: rest if invs.nonEmpty =>
            val label = Label(l.name, Nil)(pos = l.pos, l.info)
            LoopHeadBlock(invs, label :: rest)
          case stmts =>
            StatementBlock(stmts)
        }
        addBlock(index, block)
      }
      tmpStmts.clear()
    }

    private def finalizeEdge(edge: TmpEdge): SilverEdge = {
      val source = blocks(edge.source)
      val target = blocks(edge.target)
      edge match {
        case TmpUnconditionalEdge(_, _) => UnconditionalEdge(source, target)
        case TmpConditionalEdge(cond, _, _) => ConditionalEdge(cond, source, target)
      }
    }
  }

}
