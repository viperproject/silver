package silAST

trait AtomicNode extends ASTNode {
	override def subNodes(): Seq[ASTNode] = { return List.empty[ASTNode]; }
}