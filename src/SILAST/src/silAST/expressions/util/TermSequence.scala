package silAST.expressions.util

import collection.immutable.Set
import silAST.ASTNode
import silAST.expressions.terms.{GTerm, PTerm, DTerm, Term}
import silAST.symbols.logical.quantification.LogicalVariable
import silAST.programs.symbols.ProgramVariable
import silAST.source.{SourceLocation, noLocation}
import silAST.expressions.{PProgramVariableSubstitution, ProgramVariableSubstitution}
import silAST.domains._

sealed class TermSequence private[silAST](
                                           private val prArgs: Seq[Term]
                                           ) extends ASTNode with Seq[Term] {
  require(prArgs != null)
  require(prArgs.forall(_ != null))


  override val comment = Nil
  override val sourceLocation: SourceLocation = (if (prArgs.isEmpty) noLocation else prArgs.head.sourceLocation)

  def args: Seq[Term] = prArgs

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override def length = args.length

  override def toString() = "(" + args.mkString(",") + ")"

  def freeVariables: Set[LogicalVariable] = (for (a <- args) yield a.freeVariables).flatten.toSet

  def programVariables: Set[ProgramVariable] = (for (a <- args) yield a.programVariables).flatten.toSet

  def substitute(s: TypeVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))

  def substitute(s: LogicalVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))

  def substitute(s: ProgramVariableSubstitution): TermSequence = new TermSequence(for (t <- prArgs) yield t.substitute(s))
}

object TermSequence {
  //  def apply() : TermSequence = apply(List())
  def apply(ts: Term*): TermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]]: _*)
    else if (ts.forall(_.isInstanceOf[DTerm])) DTermSequence(ts.asInstanceOf[Seq[DTerm]]: _*)
    else if (ts.forall(_.isInstanceOf[PTerm])) PTermSequence(ts.asInstanceOf[Seq[PTerm]]: _*)
    else new TermSequence(ts)
  }

  def unapplySeq(ts: TermSequence) : Option[Seq[Term]] = Some(ts)
}

///////////////////////////////////////////////////////////////
sealed trait PTermSequence extends TermSequence with Seq[PTerm] {
  override def args: Seq[PTerm] = pArgs

  protected def pArgs: Seq[PTerm]

  override def apply(idx: Int): PTerm = pArgs(idx)

  override def iterator: Iterator[PTerm] = pArgs.iterator

  final override val freeVariables: Set[LogicalVariable] = Set.empty

  override def substitute(s: TypeVariableSubstitution): PTermSequence = new PTermSequenceC(for (t <- pArgs) yield t.substitute(s))

  def substitute(s: PLogicalVariableSubstitution): PTermSequence = new PTermSequenceC(for (t <- pArgs) yield t.substitute(s))

  def substitute(s: PProgramVariableSubstitution): PTermSequence = new PTermSequenceC(for (t <- pArgs) yield t.substitute(s))
}

object PTermSequence {
  //  def apply() : PTermSequence = apply(List())
  def apply(ts: PTerm*): PTermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]]: _*)
    else new PTermSequenceC(ts)
  }

  def unapplySeq(ts : PTermSequence) : Option[Seq[PTerm]] = Some(ts:Seq[PTerm])
}

private[silAST] final class PTermSequenceC(
                                            override val args: Seq[PTerm]
                                            ) extends TermSequence(args) with PTermSequence {
  override def pArgs = args

  override def apply(idx: Int) = args.apply(idx)
}

///////////////////////////////////////////////////////////////
sealed trait DTermSequence extends TermSequence with Seq[DTerm] {
  override val args: Seq[DTerm] = dArgs

  protected def dArgs: Seq[DTerm]

  override def apply(idx: Int) = dArgs(idx)

  override def iterator: Iterator[DTerm] = dArgs.iterator

  final override val programVariables = Set[ProgramVariable]()

  override def substitute(s: TypeVariableSubstitution): DTermSequence = new DTermSequenceC(for (t <- dArgs) yield t.substitute(s))

  def substitute(s: DLogicalVariableSubstitution): DTermSequence = new DTermSequenceC(for (t <- dArgs) yield t.substitute(s))
}

private[silAST] final class DTermSequenceC(
                                            override val args: Seq[DTerm]
                                            ) extends TermSequence(args) with DTermSequence {
  override val dArgs = args
}

object DTermSequence {
  def apply(ts: DTerm*): DTermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]]: _*)
    else new DTermSequenceC(ts)
  }

  def unapplySeq(ts : DTermSequence) : Option[Seq[DTerm]] = Some(ts:Seq[DTerm])
}


///////////////////////////////////////////////////////////////
final class GTermSequence private[silAST](
                                           override val args: Seq[GTerm]
                                           ) extends TermSequence(args) with DTermSequence with PTermSequence with Seq[GTerm] {
  override def apply(idx: Int) = args(idx)

  override def iterator: Iterator[GTerm] = args.iterator

  override val dArgs = args
  override val pArgs = args

  override def substitute(s: TypeVariableSubstitution): GTermSequence = new GTermSequence(for (t <- args) yield t.substitute(s))

  def substitute(s: GLogicalVariableSubstitution): GTermSequence = new GTermSequence(for (t <- args) yield t.substitute(s))
}

object GTermSequence {
  def apply(ts: GTerm*): GTermSequence = new GTermSequence(ts)
  def unapplySeq(ts : GTermSequence) : Option[Seq[GTerm]] = Some(ts:Seq[GTerm])
}

