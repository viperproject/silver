package silAST.expressions.logical.terms

import silAST.AtomicNode

trait AtomicTerm[+T <:GLogicalTerm[T]] extends GLogicalTerm[T] {
	override def subTerms : Seq[GLogicalTerm[T]] = { return Nil }
}