package silAST.expressions.terms

import silAST.AtomicNode

trait AtomicTermNode[+T <:GTermNode[T]] extends GTermNode[T] {
	override def subTerms : Seq[GTermNode[T]] = { return Nil }
}