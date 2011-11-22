package silAST

trait AtomicNode[+T <: ASTNode] extends ASTNode {
	override def subNodes(): Seq[T] = { return List.empty[T]; }
}