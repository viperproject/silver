package semper.sil.ast

import semper.sil.parser.Parser
import collection.mutable.ListBuffer

/** Utility methods for statements. */
object Statements {
  /** An empty statement. */
  val EmptyStmt = Seqn(Nil)()

  /**
   * Returns a list of all actual statements contained in a given statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def children(s: Stmt): Seq[Stmt] = {
    s match {
      case While(_, _, body) => Seq(s) ++ children(body)
      case If(_, thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case Seqn(ss) => ss
      case _ => List(s)
    }
  }
}

/** An utility object for consistency checking. */
object Consistency {

  /** Names that are not allowed for use in programs. */
  def reservedNames: Seq[String] = Parser.reserved

  /** Returns true iff the string `name` is a valid identifier. */
  def validIdentifier(name: String) = ("^" + Parser.identifier + "$").r.findFirstIn(name).isDefined

  /** Returns true iff the string `name` is a valid identifier, and not a reserved word. */
  def validUserDefinedIdentifier(name: String) = validIdentifier(name) && !reservedNames.contains(name)

  /** Returns true iff the two arguments are of equal length. */
  def sameLength[S, T](a: Seq[T], b: Seq[S]) = a.size == b.size

  /** Returns true iff the first argument can be assigned to the second one,
    * i.e. if the type of the first one is a subtype of the type of the second one. */
  def isAssignable(a: Typed, b: Typed) = a isSubtype b

  /** Returns true iff the arguments are equal of length and
    * the elements of the first argument are assignable to the corresponding elements of the second argument */
  def areAssignable(a: Seq[Typed], b: Seq[Typed]) = sameLength(a, b) && ((a zip b) forall (t => isAssignable(t._1, t._2)))

  /** Returns true iff there are no duplicates. */
  def noDuplicates[T](a: Seq[T]) = a.distinct.size == a.size

  /**
   * Is the control flow graph starting at `start` well-formed.  That is, does it have the following
   * properties:
   * <ul>
   * <li>It is acyclic.
   * <li>It has exactly one final block that all paths end in and that has no successors.
   * <li>Jumps are only within a loop, or out of (one or several) loops.
   * </ul>
   */
  // TODO: The last property about jumps is not checked as stated, but a stronger property (essentially forbidding many interesting jumps is checked)
  def isWellformedCfg(start: Block): Boolean = {
    val (ok, acyclic, terminalBlocks) = isWellformedCfgImpl(start)
    ok && acyclic && terminalBlocks.size == 1
  }

  /**
   * Implementation of well-formedness check. Returns (ok, acyclic, terminalBlocks) where `ok` refers
   * to the full graph and `acyclic` and `terminalBlocks` only to the outer-most graph (not any loops with nested
   * graphs).
   */
  private def isWellformedCfgImpl(start: Block, seenSoFar: Set[Block] = Set(), okSoFar: Boolean = true): (Boolean, Boolean, Set[TerminalBlock]) = {
    var ok = okSoFar
    start match {
      case t: TerminalBlock => (okSoFar, true, Set(t))
      case _ =>
        start match {
          case LoopBlock(body, cond, invs, succ) =>
            val (loopok, acyclic, terminalBlocks) = isWellformedCfgImpl(body)
            ok = okSoFar && loopok && acyclic && terminalBlocks.size == 1
          case _ =>
        }
        val seen = seenSoFar union Set(start)
        var terminals = Set[TerminalBlock]()
        var acyclic = true
        for (b <- start.succs) {
          if (seen contains b.dest) {
            acyclic = false
          }
          val (okrec, a, t) = isWellformedCfgImpl(b.dest, seen, ok)
          ok = ok && okrec
          acyclic = acyclic && a
          terminals = terminals union t
        }
        (ok, acyclic, terminals)
    }
  }
}

/**
 * An object that can take an AST and translate it into the corresponding CFG.
 */
object CfgGenerator {

  def toCFG(ast: Stmt): Block = {
    val p1 = new Phase1(ast)
    val p2 = new Phase2(p1)
    val p4 = new Phase4(p2)
    p4.result
  }

  trait TmpBlock {
    var pred: ListBuffer[TmpBlock] = ListBuffer()

    def +=(e: TmpEdge) {
      e.dest.pred += this
    }
  }
  class VarBlock extends TmpBlock {
    var stmts: ListBuffer[Stmt] = ListBuffer()
    var edges: ListBuffer[TmpEdge] = ListBuffer()
    override def +=(e: TmpEdge) {
      super.+=(e)
      edges += e
    }
    def stmt = if (stmts.size == 1) stmts(0) else Seqn(stmts)(NoPosition)
  }
  class TmpLoopBlock(val cond: Exp, val invs: Seq[Exp], val body: TmpBlock) extends TmpBlock {
    var edge: TmpEdge = null
    override def +=(e: TmpEdge) {
      super.+=(e)
      require(edge == null)
      edge = e
    }
  }
  trait TmpEdge {
    def dest: TmpBlock
  }
  case class CondEdge(dest: TmpBlock, cond: Exp) extends TmpEdge
  case class UncondEdge(dest: TmpBlock) extends TmpEdge

  /**
   * A label that is the target of a jump (the name identifies the target, and we
   * use a special format for labels with generated names).
   */
  case class Lbl(name: String)
  object Lbl {
    var id = 0

    def apply(name: String, generated: Boolean) = {
      id += 1
      new Lbl("$$" + name + "_" + id)
    }
  }

  /** Extended statements are used during the translation of an AST to a CFG. */
  sealed trait ExtendedStmt
  case class RegularStmt(stmt: Stmt) extends ExtendedStmt
  case class Jump(lbl: Lbl) extends ExtendedStmt
  case class CondJump(thn: Lbl, els: Lbl, cond: Exp) extends ExtendedStmt
  case class Loop(after: Lbl, cond: Exp, invs: Seq[Exp]) extends ExtendedStmt
  case class EmptyStmt() extends ExtendedStmt

  class Phase4(p3: Phase2) {
    val b2b: collection.mutable.HashMap[TmpBlock, Block] = collection.mutable.HashMap()

    def result = b2b(p3.start)

    // create a Block for every TmpBlock
    val worklist: collection.mutable.Queue[TmpBlock] = collection.mutable.Queue()
    worklist.enqueue(p3.start)
    while (!worklist.isEmpty) {
      val tb = worklist.dequeue()
      var b: Block = null
      tb match {
        case loop: TmpLoopBlock =>
          b = LoopBlock(null, loop.cond, loop.invs, null)
        case vb: VarBlock if vb.edges.size == 0 =>
          b = TerminalBlock(vb.stmt)
        case vb: VarBlock if vb.edges.size == 1 =>
          b = NormalBlock(vb.stmt, null)
        case vb: VarBlock if vb.edges.size == 2 =>
          b = ConditionalBlock(vb.stmt, vb.edges(0).asInstanceOf[CondEdge].cond, null, null)
        case _ =>
          sys.error("unexpected block")
      }
      b2b += tb -> b
    }

    // add all edges between blocks
    worklist.enqueue(p3.start)
    while (!worklist.isEmpty) {
      val tb = worklist.dequeue()
      val b: Block = b2b(tb)
      tb match {
        case loop: TmpLoopBlock =>
          val lb = b.asInstanceOf[LoopBlock]
          lb.body = b2b(loop.body)
          lb.succ = b2b(loop.edge.dest)
        case vb: VarBlock if vb.edges.size == 0 => // nothing to do, no successors
        case vb: VarBlock if vb.edges.size == 1 =>
          b.asInstanceOf[NormalBlock].succ = b2b(vb.edges(0).dest)
        case vb: VarBlock if vb.edges.size == 2 =>
          val cb = b.asInstanceOf[ConditionalBlock]
          cb.thn = b2b(vb.edges(0).dest)
          cb.els = b2b(vb.edges(1).dest)
        case _ =>
          sys.error("unexpected block")
      }
      b2b += tb -> b
    }
  }

  class Phase2(p1: Phase1) {
    val start = new VarBlock()
    var cur = start
    var nodes = p1.nodes.toSeq
    var offset = 0
    val nodeToBlock: collection.mutable.HashMap[ExtendedStmt, TmpBlock] = collection.mutable.HashMap()

    // assumes that all labels are defined
    def resolveLbl(lbl: Lbl) = nodes(lblToIdx(lbl))
    def lblToIdx(lbl: Lbl) = p1.lblmap.get(lbl).get - offset

    // a list of missing edges: every entry (stmt, f) stands for a missing edge
    // to the block that `stmt` will be part of (stmt must be a leader). the
    // function f sets the edge on the source correctly (whether it is a conditional
    // or unconditional edge).
    val missingEdges: ListBuffer[(ExtendedStmt, TmpBlock => ())] = ListBuffer()

    // run phase 2
    run()
    addMissingEdges()

    /**
     * Goes through the extended nodes in `nodes` and adds them to blocks
     * in the appropriate way.  Forward edges cannot be set yet (because the following
     * block has most likely not been constructed yet), and thus these edges are recorded
     * and added later.
     */
    private def run() {
      var i = -1
      while (i < nodes.size) {
        var b: TmpBlock = null
        nodes(i) match {
          case Jump(lbl) =>
            // finish current block and add a missing edge
            missingEdges += ((resolveLbl(lbl), _ => cur += UncondEdge(_)))
            cur = new VarBlock()
          case CondJump(thn, els, cond) =>
            // finish current block and add two missing edges
            val notCond = Not(cond)(NoPosition)
            missingEdges += ((resolveLbl(thn), _ => cur += CondEdge(_, cond)))
            missingEdges += ((resolveLbl(els), _ => cur += CondEdge(_, notCond)))
            cur = new VarBlock()
          case Loop(after, cond, invs) =>
            // handle loop body: start with a new block, and a different
            // set of nodes (the ones in the loop body), but use the same
            // missingEdges
            cur = new VarBlock()
            val oldNodes = nodes
            val oldOffset = offset
            nodes = nodes.slice(i + 1, lblToIdx(after))
            offset = i + 1
            run()
            nodes = oldNodes
            offset = oldOffset
            i = lblToIdx(after) - 1

            // create the loop block
            val loop = new TmpLoopBlock(cond, invs, cur)
            cur += UncondEdge(loop)
            cur = new VarBlock()
            loop += UncondEdge(cur)
            b = loop
          case EmptyStmt() =>
            // skip it
            b = cur
          case RegularStmt(s) =>
            cur.stmts += s
            b = cur
        }
        i += 1
        if (b != null) nodeToBlock.put(nodes(i), b)
      }
    }

    /** Add all the missing edges. */
    private def addMissingEdges() {
      for ((n, f) <- missingEdges) f(nodeToBlock(n))
    }
  }

  class Phase1(ast: Stmt) {
    /** The extended statements used in phase one. */
    val nodes: ListBuffer[ExtendedStmt] = ListBuffer()
    /** A mapping of Labels to indices into `nodes`. */
    val lblmap: collection.mutable.Map[Lbl, Int] = collection.mutable.Map()

    run(ast)
    // in case anything points to the 'next' node.
    nodes += EmptyStmt()

    /**
     * Translates a statement and adds the appropriate information to `nodes` and `lblmap`. Note that
     * every statement must extend `nodes` by at least one (so that it is OK to point to the next
     * free place in `nodes` before calling `run`).
     */
    private def run(s: Stmt) {
      s match {
        case If(cond, thn, els) =>
          val thnTarget = Lbl("then", generated = true)
          val elsTarget = Lbl("else", generated = true)
          nodes += CondJump(thnTarget, elsTarget, cond)
          lblmap += thnTarget -> nextNode
          run(thn)
          lblmap += elsTarget -> nextNode
          run(els)
        case While(cond, inv, body) =>
          val afterLoop = Lbl("afterLoop", generated = true)
          nodes += Loop(afterLoop, cond, inv)
          lblmap += afterLoop -> nextNode
        case Seqn(ss) =>
          nodes += EmptyStmt()
          for (s <- ss) run(s)
        case Goto(target) =>
          Jump(Lbl(target))
          nodes += EmptyStmt()
        case Label(name) =>
          lblmap += Lbl(name) -> nextNode
          nodes += EmptyStmt()
        case _: LocalVarAssign | _: FieldAssign |
             _: Inhale | _: Exhale |
             _: Fold | _: Unfold |
             _: MethodCall =>
          // regular, non-control statements
          nodes += RegularStmt(s)
      }
    }

    /** The index of the next extended node. */
    private def nextNode = nodes.size
  }

}

/** A utility object to visualize a control flow graph. */
object CfgVisualizer {

  /**
   * Returns a DOT representation of the control flow graph that can be visualized using
   * tools such as Graphviz.
   */
  def toDot(block: Block): String = {
    val nodes = new StringBuilder()
    val edges = new StringBuilder()

    def name(b: Block) = b.hashCode.toString
    def label(b: Block) = b match {
      case LoopBlock(_, cond, _, _) => s"while ($cond)"
      case TerminalBlock(stmt) => stmt.toString
      case NormalBlock(stmt, _) => stmt.toString
      case ConditionalBlock(stmt, cond, _, _) => s"$stmt\n\nif ($cond)"
    }

    val worklist: collection.mutable.Queue[Block] = collection.mutable.Queue()
    worklist.enqueue(block)
    while (!worklist.isEmpty) {
      val b = worklist.dequeue()

      // output node
      nodes.append("    " + name(b) + " [")
      if (b.isInstanceOf[LoopBlock]) nodes.append("shape=polygon sides=8 ");
      nodes.append("label=\""
        + label(b).replace("\\n", "\\l")
        + "\",];\n")

      // output edge and follow edges
      b match {
        case LoopBlock(body, _, _, succ) =>
          edges.append(s"    ${name(b)} -> ${name(body)};\n")
          edges.append(s"    ${name(b)} -> ${name(succ)};\n")
          worklist.enqueue(body, succ)
        case TerminalBlock(stmt) =>
        case NormalBlock(_, succ) =>
          edges.append(s"    ${name(b)} -> ${name(succ)};\n")
          worklist.enqueue(succ)
        case ConditionalBlock(_, _, thn, els) =>
          edges.append(s"    ${name(b)} -> ${name(thn)} [label=\"then\"];\n")
          edges.append(s"    ${name(b)} -> ${name(els)} [label=\"else\"];\n")
          worklist.enqueue(thn, els)
      }
    }

    val res = new StringBuilder()

    // header
    res.append("digraph {\n");
    res.append("    node [shape=rectangle];\n\n");

    // footer
    res.append("}\n");

    res.toString()
  }
}
