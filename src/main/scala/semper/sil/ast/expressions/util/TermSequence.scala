package semper.sil.ast.expressions.util

import collection.immutable.Set
import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.terms.Term
import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.programs.symbols.ProgramVariable
import semper.sil.ast.source.{SourceLocation, NoLocation}
import semper.sil.ast.expressions.ProgramVariableSubstitution
import semper.sil.ast.domains._
import semper.sil.ast.types.TypeVariable

sealed class TermSequence private[sil](
                                        private val prArgs: Seq[Term]
                                        ) extends ASTNode with Seq[Term] {
  require(prArgs != null)
  require(prArgs.forall(_ != null))


  override val comment = Nil
  override val sourceLocation: SourceLocation = (if (prArgs.isEmpty) NoLocation else prArgs.head.sourceLocation)

  def args: Seq[Term] = prArgs

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override def length = args.length

  override def toString() = "(" + args.mkString(",") + ")"

  def freeVariables: Set[LogicalVariable] = (for (a <- args) yield a.freeVariables).flatten.toSet

  def freeTypeVariables: Set[TypeVariable] = args.foldLeft(Set[TypeVariable]())(_ union _.freeTypeVariables)

  def programVariables: Set[ProgramVariable] = (for (a <- args) yield a.programVariables).flatten.toSet

  def substitute(s: TypeVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))

  def substitute(s: LogicalVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))

  def substitute(s: ProgramVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))
}

object TermSequence {
  //  def apply() : TermSequence = apply(List())
  def apply(ts: Term*): TermSequence = {
    new TermSequence(ts)
  }

  def unapplySeq(ts: TermSequence): Option[Seq[Term]] = Some(ts)
}
