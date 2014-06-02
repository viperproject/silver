package semper.sil.ast.utility

import scala.collection.mutable
import semper.sil.ast._

/** A utility object for control flow graphs. */
object ControlFlowGraph {

  /**
   * Performs a breadth-first search over a control flow graph.
   */
  def bfs(block: Block)(f: Block => Unit) {
    val worklist = collection.mutable.Queue[Block]()
    worklist.enqueue(block)
    val visited = collection.mutable.Set[Block]()

    while (!worklist.isEmpty) {
      val b = worklist.dequeue()
      // Call f(b) before collecting the successors of b,
      // thereby allowing f to modify the successors first
      f(b)
      val succsAndBody = (b.succs map (_.dest)) ++ (b match {
        case LoopBlock(body, _, _, _, _) => Seq(body)
        case ConstrainingBlock(_, body, _) => Seq(body)
        case _ => Nil
      })
      worklist.enqueue(succsAndBody filterNot visited.contains: _*)
      visited ++= succsAndBody
    }
  }

  /**
   * @see semper.sil.ast.Block#transform(PartialFunction[Block, Block])
   */
  def transform(
      block: Block,
      trans: PartialFunction[Block, Block] = PartialFunction.empty): Block = {

    // Maps old blocks to new blocks
    val map = new BlockMapping()

    // Apply the translation function to all blocks for which it is defined,
    // and shallowly copy all other blocks
    bfs(block)(block => {
      map.put(block,
        if (trans.isDefinedAt(block)) trans(block)
        else shallowCopy(block))
    })

    // Try to resolve the mapping such that it only maps to fresh blocks
    // that are not part of the original CFG
    map.resolve()

    // Use the mapping to update all block references in the new CFG
    bfs(map(block)) {
      case TerminalBlock(_) =>
      case nb @ NormalBlock(_, succ) =>
        nb.succ = map(succ)
      case cb @ ConditionalBlock(_, _, thn, els) =>
        cb.thn = map(thn)
        cb.els = map(els)
      case lb @ LoopBlock(body, _, _, _, succ) =>
        lb.body = map(body)
        lb.succ = map(succ)
      case cb @ ConstrainingBlock(_, body, succ) =>
        cb.body = map(body)
        cb.succ = map(succ)
      case _ =>
        sys.error("unexpected block")
    }

    // Return the new start block
    map(block)
  }

  /**
   * Maps blocks of the old CFG to blocks in the new CFG.
   *
   * When a block in the new CFG has a reference to a block in the old CFG,
   * this mapping will be used to update the reference.
   */
  class BlockMapping {
    private val map = mutable.HashMap[Block, Block]()

    private var _isResolved = true

    /**
     * Returns true if no original block (keys of the mapping)
     * occurs as a value in the map.
     */
    def isResolved: Boolean = _isResolved

    /**
     * Register that any reference to old block `fromBlock` should be replaced
     * by `toBLock`, or whatever `toBlock` resolves to if `toBlock` is
     * an old block itself,
     *
     * @param fromBlock block that is part of the old CFG
     * @param toBlock block that can be resolved to a fresh block by recursively
     *                applying this mapping
     */
    def put(fromBlock: Block, toBlock: Block) = {
      _isResolved = false
      map += (fromBlock -> toBlock)
    } ensuring (!isResolved)

    /**
     * Get the block that should replace any reference to `fromBlock`.
     *
     * @param fromBlock the block reference to be updated
     * @return `fromBlock` itself if `fromBlock` is not part of the old CFG
     */
    def apply(fromBlock: Block): Block = {
      require(isResolved)
      // It's also possible that some block references point to entirely fresh blocks
      // (no corresponding old blocks). In such cases, just stick to what we've found.
      map.getOrElse(fromBlock, fromBlock)
    }

    /**
     * Resolves the mapping, such that no block of the old CFG
     * (keys of the mapping) occurs as a value in the mapping.
     *
     * If a block of the old CFG occurs as a value, this function
     * recursively looks that block up in the mapping itself, until it
     * reaches a block that is not part of the old CFG.
     *
     * @throws RuntimeException if there is a cycle in the mapping (e.g. an
     *                          old block that maps to itself).
     */
    def resolve(): Unit = {
      map.transform {
        case (fromBlock, toBlock) =>
          var resolvedToBlock = toBlock
          var seenBlocks = Set.empty[Block]
          while (isOriginalBlock(resolvedToBlock) && !seenBlocks.contains(resolvedToBlock)) {
            seenBlocks = seenBlocks + resolvedToBlock
            resolvedToBlock = map(resolvedToBlock)
          }
          if (isOriginalBlock(resolvedToBlock))
            sys.error("cannot resolve block mapping with cycles")
          resolvedToBlock
      }
      _isResolved = true
    } ensuring isResolved

    private def isOriginalBlock(b: Block) = map.contains(b)
  }

  /**
   * Collects all blocks in a CFG reachable from a given Block in BFS order.
   * @param b the block to start the search from
   * @return the list of all reachable blocks
   */
  def collectBlocks(b: Block): Seq[Block] = {
    var result = List.empty[Block]
    bfs(b)(b => result = b :: result)
    result.reverse
  }

  /**
   * Shallowly copies a block, i.e., without copying referenced blocks and
   * also without copying any associated AST nodes (they are immutable anyway).
   * @param b the block to copy shallowly
   * @return the fresh block that is structurally equal to the given block
   */
  def shallowCopy(b: Block): Block = b match {
    case b: TerminalBlock => b.copy()
    case b: NormalBlock => b.copy()
    case b: ConditionalBlock => b.copy()
    case b: LoopBlock => b.copy()(b.pos, b.info)
    case b: ConstrainingBlock => b.copy()
  }

  /**
   * Checks two blocks for shallow equality, i.e. by only considering AST nodes,
   * but not referenced blocks.
   * @param b1 the first block to compare
   * @param b2 the other block to compare
   * @return true iff the blocks are shallowly equal
   */
  def shallowEq(b1: Block, b2: Block): Boolean = (b1, b2) match {
    case (TerminalBlock(stmt1), TerminalBlock(stmt2)) =>
      stmt1 == stmt2
    case (NormalBlock(stmt1, _), NormalBlock(stmt2, _)) =>
      stmt1 == stmt2
    case (ConditionalBlock(stmt1, cond1, _, _), ConditionalBlock(stmt2, cond2, _, _)) =>
      stmt1 == stmt2 && cond1 == cond2
    case (LoopBlock(_, cond1, invs1, locals1, _), LoopBlock(_, cond2, invs2, locals2, _)) =>
      cond1 == cond2 && invs1 == invs2 && locals1 == locals2
    case (ConstrainingBlock(vars1, _, _), ConstrainingBlock(vars2, _, _)) =>
      vars1 == vars2
    case (_, _) => false
  }

  /**
   * Checks two whole CFGs for structural equality, also considering all included AST nodes.
   * @param b1 the first CFG to compare
   * @param b2 the second CFG to compare
   * @return true iff the two CFGs are structurally equal
   */
  def eq(b1: Block, b2: Block): Boolean = {
    val blocks1 = collectBlocks(b1)
    val blocks2 = collectBlocks(b2)
    if (blocks1.size == blocks2.size)
      blocks1.zip(blocks2).forall { case (b, o) => shallowEq(b, o) }
    else
      false
  }

  /**
   * Returns a DOT representation of the control flow graph that can be visualized using
   * tools such as Graphviz.
   */
  def toDot(block: Block): String = {
    val nodes = new StringBuilder()
    val edges = new StringBuilder()

    def name(b: Block) = b.hashCode.toString
    def label(b: Block) = {
      val r = b match {
        case LoopBlock(_, cond, _, _, _) => s"while ($cond)"
        case ConstrainingBlock(vars, _, _) => s"constraining ($vars)"
        case TerminalBlock(stmt) => stmt.toString
        case NormalBlock(stmt, _) => stmt.toString
        case ConditionalBlock(stmt, cond, _, _) =>
          if (stmt.toString == "") s"if ($cond)"
          else s"$stmt\n\nif ($cond)"
      }
      r.replaceAll("\\n", "\\\\l")
    }

    bfs(block) {
      b =>
      // output node
        nodes.append("    " + name(b) + " [")
        if (b.isInstanceOf[LoopBlock]) nodes.append("shape=polygon sides=8 ")
        nodes.append("label=\""
          + label(b)
          + "\",];\n")

        // output edge and follow edges
        b match {
          case LoopBlock(body, _, _, _, succ) =>
            edges.append(s"    ${name(b)} -> ${name(body)} " + "[label=\"body\"];\n")
            edges.append(s"    ${name(b)} -> ${name(succ)} " + "[label=\"endLoop\"];\n")
          case ConstrainingBlock(_, body, succ) =>
            edges.append(s"    ${name(b)} -> ${name(body)} " + "[label=\"body\"];\n")
            edges.append(s"    ${name(b)} -> ${name(succ)} " + "[label=\"succ\"];\n")
          case TerminalBlock(stmt) =>
          case NormalBlock(_, succ) =>
            edges.append(s"    ${name(b)} -> ${name(succ)};\n")
          case ConditionalBlock(_, _, thn, els) =>
            edges.append(s"    ${name(b)} -> ${name(thn)} " + "[label=\"then\"];\n")
            edges.append(s"    ${name(b)} -> ${name(els)} " + "[label=\"else\"];\n")
        }
    }

    val res = new StringBuilder()

    // header
    res.append("digraph {\n")
    res.append("    node [shape=rectangle];\n\n")

    res.append(nodes)
    res.append(edges)

    // footer
    res.append("}\n")

    res.toString()
  }

  /**
   * Computes the set of variables that are written to, but not declared, in the given block.
   * @param b A block whose set of written variables is to be computed.
   * @return The set of written variables.
   */
  def writtenVars(b: Block): Seq[LocalVar] = {
    val writtenTo = b match {
      case lb: LoopBlock => writtenVars(lb.body)
      case cb: ConditionalBlock => cb.stmt.writtenVars ++ writtenVars(cb.thn) ++ writtenVars(cb.els)
      case cb: ConstrainingBlock => writtenVars(cb.body) ++ cb.vars
      case sb: StatementBlock => sb.stmt.writtenVars
    }

    writtenTo.distinct
  }
}
