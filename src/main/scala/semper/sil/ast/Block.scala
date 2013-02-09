package semper.sil.ast

/** A common trait for basic blocks. */
sealed trait Block extends Node with Positioned with Infoed {
  // A unique ID for basic blocks to define a good hash function
  private val id = {
    Block.id
    Block.id += 1
  }
  def succs: Seq[Edge]
  final override def equals(o: Any) = o match {
    case o: AnyRef => this eq o
    case _ => false
  }
  final override def hashCode = id.hashCode
}
object Block {
  private var id: Int = 0
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
case class TerminalBlock(stmt: Stmt)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Block {
  lazy val succs = Nil
}

/** A basic block with one outgoing edges. */
case class NormalBlock(stmt: Stmt, succ: Block)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Block {
  lazy val succs = List(UnconditionalEdge(succ))
}

/** A basic block with two outgoing edges that are conditional. */
case class ConditionalBlock(stmt: Stmt, cond: Exp, thn: Block, els: Block)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Block {
  lazy val succs = List(ConditionalEdge(thn, cond), ConditionalEdge(els, Not(cond)(NoPosition)))
}

/** A loop block with an implicit conditional back edge, and one unconditional outgoing edge. */
case class LoopBlock(body: Block, cond: Exp, invs: Seq[Exp], succ: Block)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Block {
  lazy val succs = List(UnconditionalEdge(succ))
}
