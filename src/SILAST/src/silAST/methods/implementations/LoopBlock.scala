package silAST.methods.implementations

import silAST.methods.Scope
import silAST.source.SourceLocation
import silAST.expressions.{PExpression, Expression}
import silAST.programs.symbols.ProgramVariable

final class LoopBlock private[silAST]
  (
    lbFactory: LoopBlockFactory,
    override val cfg : ControlFlowGraph,
    override val implementation : Implementation,
    override val label : String,
    pParentScope : Scope,
    val condition : PExpression
  )
  (val sourceLocation: SourceLocation)
  extends Block
  with Scope
{
  /////////////////////////////////////////////////////////////////////////////////////
  override val factory = lbFactory
  override val parentScope = Some(pParentScope)

  val bodyFactory = new CFGFactory(implementation,this)(sourceLocation)
  def body = bodyFactory.cfg
  def invariant : Expression = pInvariant match { case Some(e) => e case _ => throw new Exception() }
  
  private[silAST] var pInvariant : Option[Expression] = None

  override def readVariables : Set[ProgramVariable] =
    (for (n <- cfg.nodes) yield n.readVariables ).flatten.toSet union
    invariant.programVariables union
    condition.programVariables
  override def writtenVariables : Set[ProgramVariable] =
    (for (n <- cfg.nodes) yield n.writtenVariables ).flatten.toSet //TODO:is this enough?

  /////////////////////////////////////////////////////////////////////////////////////
  override def toString = label + ": while " + condition + " do {" + body.toString + "} " + controlFlowToString
  override def hashCode = toString.hashCode()
  override def equals(other:Any) = other match { case lb : LoopBlock => this eq lb case _ => false}
}
