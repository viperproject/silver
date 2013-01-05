package semper.sil.ast.methods.implementations

import semper.sil.ast.methods.Scope
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.{Expression}
import semper.sil.ast.programs.symbols.ProgramVariable

final class LoopBlock private[sil]
(
  lbFactory: LoopBlockFactory,
  override val cfg: ControlFlowGraph,
  override val implementation: Implementation,
  override val label: String,
  pParentScope: Scope,
  val condition: Expression
  )
(val sourceLocation: SourceLocation, val comment: List[String])
  extends Block
  with Scope {
  /////////////////////////////////////////////////////////////////////////////////////
  override val factory = lbFactory
  override val parentScope = Some(pParentScope)

  val bodyFactory = new CFGFactory(implementation, this)(sourceLocation)

  def body = bodyFactory.cfg

  def invariant: Expression = pInvariant match {
    case Some(e) => e
    case _ => throw new Exception()
  }

  private[sil] var pInvariant: Option[Expression] = None

  override def readVariables: Set[ProgramVariable] =
    (for (n <- body.nodes) yield n.readVariables).flatten.toSet union
      invariant.programVariables union
      condition.programVariables

  override def writtenVariables: Set[ProgramVariable] =
    (for (n <- body.nodes) yield n.writtenVariables).flatten.toSet //TODO:is this enough?

  /////////////////////////////////////////////////////////////////////////////////////
  override def toString = label + ": while " + condition + sys.props("line.separator") +
    (pInvariant match {
      case Some(e) => " -- invariant: " + e.toString + sys.props("line.separator")
      case _ => ""
    }) +
    "  do {" + body.toString + "} " + controlFlowToString

  override def hashCode() = toString.hashCode()

  override def equals(other: Any) = other match {
    case lb: LoopBlock => this eq lb
    case _ => false
  }
}
