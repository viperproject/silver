/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.sil.ast

import utility.ControlFlowGraph
import utility.AstGenerator

/** A common trait for basic blocks. */
sealed trait Block {
  def succs: Seq[Edge]
  final override def equals(o: Any) = o match {
    case o: AnyRef => this eq o
    case _ => false
  }
  final override def hashCode = System.identityHashCode(this)

  /**
   * Returns a DOT representation of the control flow graph that can be visualized using
   * tools such as Graphviz.
   */
  def toDot = ControlFlowGraph.toDot(this)

  /**
   * Returns an AST representation of this control flow graph.
   */
  def toAst = AstGenerator.toAst(this)

  /**
   * See [[semper.sil.ast.utility.ControlFlowGraph.writtenVars]]
   */
  def writtenVars = ControlFlowGraph.writtenVars(this)

  /**
   * Transforms a CFG by applying a partial translation function to each block
   * and copying all blocks for which the translation function is not defined.
   *
   * Possible transformations include:
   *
   * 1. Replace blocks, for example to use different AST nodes like conditions
   *    or to use a different type of block.
   *    Example: Simplify all ConditionalBlocks whose condition is true.
   *
   *    cfg.transform({
   *      case ConditionalBlock(stmt, TrueLit(), thn, els) =>
   *        NormalBlock(stmt, thn)
   *    })
   *
   *    Any reference to the old ConditionalBlock (in its predecessors)
   *    will point to the newly created NormalBlock in the new CFG.
   *
   *    Note that the newly created NormalBlock refers to the block `thn`
   *    in the old CFG. This reference will be resolved to whatever the
   *    block `thn` is translated to.
   *
   *    If the block `els` is not referenced by any other blocks, its
   *    translation will not be part of the newly constructed CFG.
   *
   * 2. Remove certain blocks
   *    val blockToRemove: NormalBlock = ...
   *    cfg.transform({
   *      case b @ NormalBlock(stmt, succ) if b == blockToRemove =>
   *        succ
   *    })
   *
   *    Any reference to the old NormalBlock (in its predecessors)
   *    will be replaced by a direct reference to the translation of `succ`.
   *
   * 3. Add new block
   *    Example: Add a new statement at the beginning of the body of each loop
   *    Since the body may be a block without a sequence of statements,
   *    the easiest way to do so is to prepend a NormalBlock to the body.
   *
   *    val newStmt: Stmt = ...
   *    cfg.transform({
   *      case lb @ LoopBlock(body, cond, invs, locals, succ) =>
   *        LoopBlock(NormalBlock(stmt, body), cond, invs, locals, succ)
   *    })
   *
   *    Again, the references to `body` and `succ` will be replaced later
   *    with whatever `body` and `succ` are translated to, respectively.
   *
   * Beware of cycles in the mapping or blocks defined by the translation!
   * Never directly return the exact reference to the old block itself.
   * Otherwise, the call will throw an exception.
   * To solve the problem, shallowly copy the block instead.
   *
   * The reason is that any reference to an old block in the new CFG
   * needs to be resolved to a block that does not occur in the old CFG
   * (to ensure that the two CFGs are disjoint).
   *
   * @param trans the partial translation function, as shown in the examples
   * @return the newly constructed, completely disjoint CFG
   * @throws RuntimeException if a reference to a block in the old CFG cannot
   *                          be resolved to a block that does not occur in
   *                          the old CFG. See comment above.
   */
  def transform(trans: PartialFunction[Block, Block] = PartialFunction.empty): Block =
    ControlFlowGraph.transform(this, trans)

  /**
   * Shallowly copies the block, i.e., without copying referenced blocks and
   * also without copying any associated AST nodes (they are immutable anyway).
   * @return the fresh block that is structurally equal to this block
   */
  def copyShallow(): Block =
    ControlFlowGraph.shallowCopy(this)
}

object Block {
  private var id: Int = 0
}

/**
 * A statement block is a block whose body contains a statement, which is the most common type
 * of blocks.
 */
sealed trait StatementBlock extends Block {
  def stmt: Stmt
}

object StatementBlock {
  def unapply(sb: StatementBlock) = Some((sb.stmt, sb.succs))
}

/** A control flow edge. */
sealed trait Edge {
  def dest: Block
}

/** A conditional control flow edge. */
case class ConditionalEdge(dest: Block, cond: Exp) extends Edge

/** An unconditional control flow edge. */
case class UnconditionalEdge(dest: Block) extends Edge

/** A basic block without outgoing edges. */
case class TerminalBlock(stmt: Stmt) extends StatementBlock {
  lazy val succs = Nil
}

/** A basic block with one outgoing edges. */
case class NormalBlock(stmt: Stmt, var succ: Block) extends StatementBlock {
  // Do not use `lazy val` because `succ` could potentially be modified
  // during construction of the CFG. Using `def` mitigates the danger of
  // returning stale data.
  def succs = List(UnconditionalEdge(succ))
}

/** A basic block with two outgoing edges that are conditional. */
case class ConditionalBlock(stmt: Stmt, cond: Exp, var thn: Block, var els: Block) extends StatementBlock {
  def succs = List(ConditionalEdge(thn, cond), ConditionalEdge(els, Not(cond)(NoPosition)))
}

/** A loop block with an implicit conditional back edge, and one unconditional outgoing edge. */
case class LoopBlock(var body: Block, cond: Exp, invs: Seq[Exp], locals: Seq[LocalVarDecl], var succ: Block)
                    (val pos: Position = NoPosition, val info: Info = NoInfo)
      extends Block {

  /* Note: It is the responsibility of the user of LoopBlock to ensure that the srcAst
   * can actually be used instead of computing it from the LoopBlock (via Block.toAst).
   * For example, the srcAst might not be in sync with the LoopBlock anymore if the
   * body or the invariant of the block is changed after the block has been created
   * from the srcAst.
   */
  private[ast] var srcAst: Option[While] = None
  override lazy val toAst = srcAst.getOrElse(super.toAst)

  def succs = List(UnconditionalEdge(succ))
}

/** Corresponds to the `Constraining` statement, that is, the `vars` can be constrained inside the `body`. */
case class ConstrainingBlock(vars: Seq[LocalVar], var body: Block, var succ: Block) extends Block {
  def succs = List(UnconditionalEdge(succ))
}
