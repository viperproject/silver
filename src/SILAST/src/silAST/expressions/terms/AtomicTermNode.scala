package silAST.expressions.terms

import silAST.AtomicNode

trait AtomicTermNode[+T <:AtomicTermNode[T]] extends TermNode[T] {
	override def subTerms : Seq[T] = { return Nil }
}