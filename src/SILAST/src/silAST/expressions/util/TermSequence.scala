package silAST.expressions.util

import silAST.ASTNode
import silAST.expressions.terms.{GTerm, PTerm, DTerm, Term}
import silAST.source.noLocation
import silAST.symbols.logical.quantification.BoundVariable
import silAST.programs.symbols.ProgramVariable

sealed class TermSequence private[silAST](
                                           private val prArgs: Seq[Term]
                                           ) extends ASTNode(noLocation) with Seq[Term]
{
  def args : Seq[Term] = prArgs
  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override def length = args.length
  override def toString = "(" + args.mkString(",") + ")"
  override def subNodes = args

  def freeVariables    : collection.immutable.Set[BoundVariable]   = (for (a <- args) yield a.freeVariables).flatten.toSet
  def programVariables : collection.immutable.Set[ProgramVariable] = (for (a <- args) yield a.programVariables).flatten.toSet

}

object TermSequence{
//  def apply() : TermSequence = apply(List())
  def apply(ts : Term*) : TermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]] : _*)
    else if (ts.forall(_.isInstanceOf[DTerm])) DTermSequence(ts.asInstanceOf[Seq[DTerm]] : _*)
    else if (ts.forall(_.isInstanceOf[PTerm])) PTermSequence(ts.asInstanceOf[Seq[PTerm]] : _*)
    else new TermSequence(ts)
  }
}

///////////////////////////////////////////////////////////////
sealed trait PTermSequence extends TermSequence with Seq[PTerm] {
  override def args : Seq[PTerm] = pArgs

  protected def pArgs: Seq[PTerm]

  override def apply(idx: Int): PTerm = pArgs(idx)

  override def iterator : Iterator[PTerm] = pArgs.iterator
  final override val freeVariables : Set[BoundVariable] = Set.empty
}

object PTermSequence{
//  def apply() : PTermSequence = apply(List())
  def apply(ts : PTerm*) : PTermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]] : _*)
    else new PTermSequenceC(ts)
  }
}

private [silAST] final class PTermSequenceC(
                                            override val args: Seq[PTerm]
                                            ) extends TermSequence(args) with PTermSequence
{
  override def pArgs = args
  override def apply(idx:Int) = args.apply(idx)
}

///////////////////////////////////////////////////////////////
sealed trait DTermSequence extends TermSequence with Seq[DTerm] {
  override val args : Seq[DTerm] = dArgs

  protected def dArgs: Seq[DTerm]

  override def apply(idx: Int) = dArgs(idx)

  override def iterator : Iterator[DTerm] = dArgs.iterator
  final override val programVariables = Set[ProgramVariable]()
}

private [silAST] final class DTermSequenceC(
                                            override val args: Seq[DTerm]
                                            ) extends TermSequence(args) with DTermSequence
{
  override val dArgs = args
}

object DTermSequence{
  def apply(ts : DTerm*) : DTermSequence = {
    if (ts.forall(_.isInstanceOf[GTerm])) GTermSequence(ts.asInstanceOf[Seq[GTerm]] : _*)
     else new DTermSequenceC(ts)
  }
}


///////////////////////////////////////////////////////////////
final class GTermSequence private[silAST](
                                           override val args: Seq[GTerm]
                                           ) extends TermSequence(args) with DTermSequence with PTermSequence with Seq[GTerm] {
  override def apply(idx: Int) = args(idx)

  override def iterator : Iterator[GTerm] = args.iterator

  override val dArgs = args
  override val pArgs = args
}

object GTermSequence{
  def apply(ts : GTerm*) : GTermSequence = new GTermSequence(ts)
}

