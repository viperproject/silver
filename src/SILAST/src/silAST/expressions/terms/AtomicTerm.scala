package silAST.expressions.terms

import silAST.AtomicNode

trait AtomicTerm[+T <:GTerm[T]] extends GTerm[T] {
	override def subTerms : Seq[GTerm[T]] = { return Nil }
}