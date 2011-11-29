package silAST.expressions.util

import silAST.expressions.terms.ProgramTerm

abstract class PArgumentSequence extends ArgumentSequence {
  override val args: Seq[ProgramTerm]

  override def asSeq: Seq[ProgramTerm] = args
}