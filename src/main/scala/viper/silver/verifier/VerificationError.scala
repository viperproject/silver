// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.verifier

import fastparse.Parsed
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Rewritable


/**********************************************************************************
  * IMPORTANT:
  * After changing this file, please edit the corresponding JSON convertors in:
  *  viper/server/frontends/http/jsonWriters/ViperIDEProtocol.scala
  *  https://github.com/viperproject/viperserver
  **********************************************************************************/

sealed trait ModelEntry

sealed trait ValueEntry extends ModelEntry

case object UnspecifiedEntry extends ValueEntry {
  override def toString: String = "#unspecified"
}

case class ConstantEntry(value: String) extends ValueEntry {
  override def toString: String = value
}

case class ApplicationEntry(name: String, arguments: Seq[ValueEntry]) extends ValueEntry {
  override def toString: String = s"($name ${arguments.mkString(" ")})"
}

case class MapEntry(options: Map[Seq[ValueEntry], ValueEntry], default: ValueEntry) extends ModelEntry {
  override def toString: String = {
    if (options.nonEmpty)
      "{\n" + options.map(o => "    " + o._1.mkString(" ") + " -> " + o._2).mkString("\n") + "\n    else -> " + default +"\n}"
    else
      "{\n    " + default +"\n}"
  }

  /**
   * Tries to parse this entry as a function definition, e.g.
   * name -> {  (or
   *                (and (= (:var 0) v1) (= (:var 1) v2))
   *                (and (= (:var 0) v3) (= (:var 1) v4))
   *             )
   * }
   * If this succeeds, converts the entry to the "normal" form
   * name -> {
   *   v1 v2 -> true
   *   v3 v4 -> true
    *  else -> false
   * }
   * Otherwise returns the original entry unchanged.
   */
  def resolveFunctionDefinition = {
    if (options.isEmpty && default.isInstanceOf[ApplicationEntry]) {
      parseArgConstraintDisjunction(default) match {
        case Some(vvs) => {
          MapEntry(vvs.map(args => args -> ConstantEntry("true")).toMap, ConstantEntry("false"))
        }
        case None => this
      }
    }else{
      this
    }
  }

  def parseArgConstraintDisjunction(e: ValueEntry) = e match {
    case ApplicationEntry("or", arguments) => {
      val args = arguments.map(parseArgConstraintConjunction)
      if (args.forall(_.isDefined)) {
        val values = args.map(_.get)
        Some(values)
      }else{
        None
      }
    }
    case _ => parseArgConstraintConjunction(e) match {
      case Some(vs) => Some(Seq(vs))
      case None => None
    }
  }

  def parseArgConstraintConjunction(ae: ValueEntry) = ae match {
    case ApplicationEntry("and", arguments) => {
      val args = arguments.map(parseSingleArgConstraint)
      if (args.forall(_.isDefined)) {
        val indices = args.map(_.get._1)
        // We expect the arguments in the order 0, 1, ..., n-1; if we get something else, reject.
        // TODO: Find out if this order is always guaranteed,
        if (indices != (0 until indices.size).map(_.toString))
          None
        else
          Some(args.map(_.get._2))
      }else{
        None
      }
    }
    case _ => parseSingleArgConstraint(ae) match {
      case Some(("0", v)) => Some(Seq(v))
      case _ => None
    }
  }

  def parseSingleArgConstraint(ae: ValueEntry) = ae match {
    case ApplicationEntry("=", Seq(ApplicationEntry(":var", Seq(ConstantEntry(index))), v)) => Some(index, v)
    case _ => None
  }
}
case class Model(entries: Map[String, ModelEntry]) {
  override def toString: String = entries.map(e => e._1 + " -> " + e._2).mkString("\n")
}

trait Counterexample {
  val model: Model
  override def toString: String = model.toString
}

case class SimpleCounterexample(model: Model) extends Counterexample

trait CounterexampleTransformer {
  def f: Counterexample => Counterexample
}

object CounterexampleTransformer {
  def apply(ff: Counterexample => Counterexample): CounterexampleTransformer = {
    new CounterexampleTransformer {
      def f: Counterexample => Counterexample = ff
    }
  }
}

object Model {
  def apply(modelString: String) : Model = {
    fastparse.parse(modelString, ModelParser.model(_)) match {
      case Parsed.Success(model, _) => model
      case failure: Parsed.Failure => throw new Exception(failure.toString)
    }
  }
}

trait ErrorMessage {
  def id: String
  def offendingNode: errors.ErrorNode
  def pos: Position
  def readableMessage: String

  // Should consider refactoring as a transformer, if/once we make the error message structure recursive
  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) : ErrorMessage

  // Check if the offendingNode contains any `FailureExpectedInfo` info tags
  def isExpected: Boolean = offendingNode match {
    case i: Infoed => i.info.getUniqueInfo[FailureExpectedInfo].isDefined
    case _ => false
  }
}

sealed trait VerificationError extends AbstractError with ErrorMessage {
  def reason: ErrorReason
  def readableMessage(withId: Boolean = false, withPosition: Boolean = false): String
  override def readableMessage: String = {
    val msg = readableMessage(false, true)
    if (failureContexts.isEmpty)
      msg
    else
      msg + "\n" + failureContexts.map(e => e.toString).mkString("\n")
  }
  def loggableMessage: String = s"$fullId-$pos" + (if (cached) "-cached" else "")
  def fullId = s"$id:${reason.id}"
  var failureContexts: Seq[FailureContext] = Seq() //TODO: make immutable

}

trait FailureContext {
  def counterExample: Option[Counterexample]
  def toString: String
}

/// used when an error/reason has no sensible node to use
case object DummyNode extends Node with Positioned with TransformableErrors with Rewritable {
  val pos = NoPosition
  val info = NoInfo
  val errT = NoTrafos
}

/// used when an error has no sensible reason
case object DummyReason extends AbstractErrorReason {
  val id = "?"
  val readableMessage = "?"
  val offendingNode = DummyNode
  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = DummyReason
}

sealed trait ErrorReason extends ErrorMessage

trait PartialVerificationError {
  def f: ErrorReason => VerificationError

  def dueTo(reason: ErrorReason) = f(reason)

  // apply a transformation to the node attached to the eventually-supplied error reason (note: not currently to other parameters, nor to the node attached to the error itself)
  def withReasonNodeTransformed(t : errors.ErrorNode => errors.ErrorNode) = {
    PartialVerificationError(
      (r:ErrorReason) =>
      f(r.withNode(t(r.offendingNode)).asInstanceOf[ErrorReason])
    )
  }

  override lazy val toString = f(DummyReason).readableMessage(true, true)
}

object PartialVerificationError { // Note: the apply method is used here to instantiate the kind of PartialVerificationError, not to apply it to an ErrorReason (for which we have dueTo(..))
  def apply(ff: ErrorReason => VerificationError) = {
    new PartialVerificationError {
      def f: (ErrorReason) => VerificationError = ff
    }
  }
}

case object NullPartialVerificationError extends PartialVerificationError {
  def f = _ => null
}

sealed abstract class AbstractVerificationError extends VerificationError {
  protected def text: String

  def pos = offendingNode.pos

  def readableMessage(withId: Boolean, withPosition: Boolean) = {
    val idStr = if (withId) s"[$fullId] " else ""
    val posStr = if (withPosition) s" ($pos)" else ""

    s"$idStr$text ${reason.readableMessage}$posStr"
  }

  /** Transform the error back according to the specified error transformations */
  override def transformedError(): AbstractVerificationError = {
    val errorT = offendingNode.transformError(this)
    val reasonT = errorT.reason.offendingNode.transformReason(errorT.reason)

    val res = errorT.withReason(reasonT)
    res.failureContexts = failureContexts
    res
  }

  def withReason(reason: ErrorReason): AbstractVerificationError

  override def toString = readableMessage(true, true) + (if (cached) " - cached" else "")
}

abstract class ExtensionAbstractVerificationError extends AbstractVerificationError

sealed abstract class AbstractErrorReason extends ErrorReason {
  def pos = offendingNode.pos
  override def toString = readableMessage
}

abstract class ExtensionAbstractErrorReason extends AbstractErrorReason

object errors {
  type ErrorNode = Node with Positioned with TransformableErrors with Rewritable

  case class Internal(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = Internal(offendingNode, this.reason, this.cached)
    def withReason(r: ErrorReason) = Internal(offendingNode, r, cached)
  }
  // internal errors can be created with dummy nodes
  def Internal(reason: ErrorReason) : Internal = Internal(DummyNode, reason)
  def Internal(offendingNode: ErrorNode = DummyNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => Internal(offendingNode, reason))

  case class AssignmentFailed(offendingNode: AbstractAssign, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "assignment.failed"
    val text = "Assignment might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = AssignmentFailed(offendingNode.asInstanceOf[AbstractAssign], this.reason, this.cached)
    def withReason(r: ErrorReason) = AssignmentFailed(offendingNode, r, cached)
  }

  def AssignmentFailed(offendingNode: AbstractAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssignmentFailed(offendingNode, reason))

  case class CallFailed(offendingNode: MethodCall, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "call.failed"
    val text = "Method call might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = CallFailed(offendingNode.asInstanceOf[MethodCall], this.reason, this.cached)
    def withReason(r: ErrorReason) = CallFailed(offendingNode, r, cached)
  }

  def CallFailed(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => CallFailed(offendingNode, reason))

  case class ContractNotWellformed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "not.wellformed"
    val text = s"Contract might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ContractNotWellformed(offendingNode.asInstanceOf[Exp], this.reason, this.cached)
    def withReason(r: ErrorReason) = ContractNotWellformed(offendingNode, r, cached)
  }

  def ContractNotWellformed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ContractNotWellformed(offendingNode, reason))

  case class PreconditionInCallFalse(offendingNode: MethodCall, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "call.precondition"
    val text = s"The precondition of method ${offendingNode.methodName} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PreconditionInCallFalse(offendingNode.asInstanceOf[MethodCall], this.reason, this.cached)
    def withReason(r: ErrorReason) = PreconditionInCallFalse(offendingNode, r, cached)
  }

  def PreconditionInCallFalse(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInCallFalse(offendingNode, reason))

  case class PreconditionInAppFalse(offendingNode: FuncApp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "application.precondition"
    val text = s"Precondition of function ${offendingNode.funcname} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PreconditionInAppFalse(offendingNode.asInstanceOf[FuncApp], this.reason, this.cached)
    def withReason(r: ErrorReason) = PreconditionInAppFalse(offendingNode, r, cached)
  }

  case class ErrorWrapperWithExampleTransformer(wrappedError: AbstractVerificationError, transformer: CounterexampleTransformer) extends AbstractVerificationError {
    val id = wrappedError.id
    val text = "Wrapped error, should be unwrapped"
    val offendingNode = wrappedError.offendingNode
    val reason = wrappedError.reason

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
      ErrorWrapperWithExampleTransformer(wrappedError.withNode(offendingNode).asInstanceOf[AbstractVerificationError], transformer)

    def withReason(r: ErrorReason) = ErrorWrapperWithExampleTransformer(wrappedError.withReason(r), transformer)

    override def readableMessage(withId: Boolean, withPosition: Boolean) = wrappedError.readableMessage(withId, withPosition)
  }

  def PreconditionInAppFalse(offendingNode: FuncApp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInAppFalse(offendingNode, reason))

  def ErrorWrapperWithExampleTransformer(pve: PartialVerificationError, transformer: CounterexampleTransformer) : PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ErrorWrapperWithExampleTransformer(pve.f(reason).asInstanceOf[AbstractVerificationError], transformer))

  case class ExhaleFailed(offendingNode: Exhale, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "exhale.failed"
    val text = "Exhale might fail."

    override def pos = offendingNode.exp.pos
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ExhaleFailed(offendingNode.asInstanceOf[Exhale], this.reason, this.cached)
    def withReason(r: ErrorReason) = ExhaleFailed(offendingNode, r, cached)
  }

  def ExhaleFailed(offendingNode: Exhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ExhaleFailed(offendingNode, reason))

  case class InhaleFailed(offendingNode: Inhale, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "inhale.failed"
    val text = "Inhale might fail."

    override def pos = offendingNode.exp.pos
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InhaleFailed(offendingNode.asInstanceOf[Inhale], this.reason, this.cached)
    def withReason(r: ErrorReason) = InhaleFailed(offendingNode, r, cached)
  }

  def InhaleFailed(offendingNode: Inhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => InhaleFailed(offendingNode, reason))

  case class IfFailed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "if.failed"
    val text = "Conditional statement might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = IfFailed(offendingNode.asInstanceOf[Exp], this.reason, this.cached)
    def withReason(r: ErrorReason) = IfFailed(offendingNode, r, cached)
  }

  def IfFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => IfFailed(offendingNode, reason))

  case class WhileFailed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "while.failed"
    val text = "While statement might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = WhileFailed(offendingNode.asInstanceOf[Exp], this.reason, this.cached)
    def withReason(r: ErrorReason) = WhileFailed(offendingNode, r, cached)
  }

  def WhileFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => WhileFailed(offendingNode, reason))

  case class AssertFailed(offendingNode: Assert, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "assert.failed"
    val text = "Assert might fail."

    override def pos = offendingNode.exp.pos
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = AssertFailed(offendingNode.asInstanceOf[Assert], this.reason, this.cached)
    def withReason(r: ErrorReason) = AssertFailed(offendingNode, r, cached)
  }

  def AssertFailed(offendingNode: Assert): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertFailed(offendingNode, reason))

  case class TerminationFailed(offendingNode: Function, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "termination.failed"
    val text = s"Function ${offendingNode.name} might not terminate."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationFailed(offendingNode.asInstanceOf[Function], this.reason, this.cached)
    def withReason(r: ErrorReason) = TerminationFailed(offendingNode, r, cached)
  }

  def TerminationFailed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((r: ErrorReason) => TerminationFailed(offendingNode, r))

  case class PostconditionViolated(offendingNode: Exp, member: Contracted, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "postcondition.violated"
    val text = s"Postcondition of ${member.name} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PostconditionViolated(offendingNode.asInstanceOf[Exp], this.member, this.reason, this.cached)
    def withReason(r: ErrorReason) = PostconditionViolated(offendingNode, member, r, cached)
  }

  def PostconditionViolated(offendingNode: Exp, member: Contracted): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, member, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FoldFailed(offendingNode.asInstanceOf[Fold], this.reason, this.cached)
    def withReason(r: ErrorReason) = FoldFailed(offendingNode, r, cached)
  }

  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = UnfoldFailed(offendingNode.asInstanceOf[Unfold], this.reason, this.cached)
    def withReason(r: ErrorReason) = UnfoldFailed(offendingNode, r, cached)
  }

  def UnfoldFailed(offendingNode: Unfold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnfoldFailed(offendingNode, reason))

  case class PackageFailed(offendingNode: Package, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "package.failed"
    val text = s"Packaging wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PackageFailed(offendingNode.asInstanceOf[Package], this.reason, this.cached)
    def withReason(r: ErrorReason) = PackageFailed(offendingNode, r, cached)
  }

  def PackageFailed(offendingNode: Package): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PackageFailed(offendingNode, reason))

  case class ApplyFailed(offendingNode: Apply, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "apply.failed"
    val text = s"Applying wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ApplyFailed(offendingNode.asInstanceOf[Apply], this.reason, this.cached)
    def withReason(r: ErrorReason) = ApplyFailed(offendingNode, r, cached)
  }

  def ApplyFailed(offendingNode: Apply): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ApplyFailed(offendingNode, reason))

  case class LoopInvariantNotPreserved(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "invariant.not.preserved"
    val text = s"Loop invariant $offendingNode might not be preserved."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LoopInvariantNotPreserved(offendingNode.asInstanceOf[Exp], this.reason, this.cached)
    def withReason(r: ErrorReason) = LoopInvariantNotPreserved(offendingNode, r, cached)
  }

  def LoopInvariantNotPreserved(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotPreserved(offendingNode, reason))

  case class LoopInvariantNotEstablished(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "invariant.not.established"
    val text = s"Loop invariant $offendingNode might not hold on entry."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LoopInvariantNotEstablished(offendingNode.asInstanceOf[Exp], this.reason, this.cached)
    def withReason(r: ErrorReason) = LoopInvariantNotEstablished(offendingNode, r, cached)
  }

  def LoopInvariantNotEstablished(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotEstablished(offendingNode, reason))

  case class FunctionNotWellformed(offendingNode: Function, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "function.not.wellformed"
    val text = s"Function might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FunctionNotWellformed(offendingNode.asInstanceOf[Function], this.reason, this.cached)
    def withReason(r: ErrorReason) = FunctionNotWellformed(offendingNode, r, cached)
  }

  def FunctionNotWellformed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FunctionNotWellformed(offendingNode, reason))

  case class PredicateNotWellformed(offendingNode: Predicate, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "predicate.not.wellformed"
    val text = s"Predicate might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PredicateNotWellformed(offendingNode.asInstanceOf[Predicate], this.reason, this.cached)
    def withReason(r: ErrorReason) = PredicateNotWellformed(offendingNode, r, cached)
  }

  def PredicateNotWellformed(offendingNode: Predicate): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PredicateNotWellformed(offendingNode, reason))

  case class MagicWandNotWellformed(offendingNode: MagicWand, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "wand.not.wellformed"
    val text = s"Magic wand might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = MagicWandNotWellformed(offendingNode.asInstanceOf[MagicWand], this.reason, this.cached)
    def withReason(r: ErrorReason) = MagicWandNotWellformed(offendingNode, r, cached)
  }

  def MagicWandNotWellformed(offendingNode: MagicWand): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => MagicWandNotWellformed(offendingNode, reason))

  case class LetWandFailed(offendingNode: LocalVarAssign, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "letwand.failed"
    val text = s"Referencing a wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LetWandFailed(offendingNode.asInstanceOf[LocalVarAssign], this.reason, this.cached)
    def withReason(r: ErrorReason) = LetWandFailed(offendingNode, r, cached)
  }

  def LetWandFailed(offendingNode: LocalVarAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LetWandFailed(offendingNode, reason))

  case class QuasihavocFailed(offendingNode: Quasihavoc, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "quasihavoc.failed"
    val text = "Quasihavoc might fail."

    override val pos = offendingNode.exp.pos
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = QuasihavocFailed(offendingNode.asInstanceOf[Quasihavoc], this.reason, this.cached)
    def withReason(r: ErrorReason) = QuasihavocFailed(offendingNode, r, cached)
  }

  def QuasihavocFailed(offendingNode: Quasihavoc): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => QuasihavocFailed(offendingNode, reason))

  case class HavocallFailed(offendingNode: Quasihavocall, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "quasihavocall.failed"
    val text = "Quasihavocall might fail."

    override val pos = offendingNode.exp.pos
    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = HavocallFailed(offendingNode.asInstanceOf[Quasihavocall], this.reason, this.cached)
    def withReason(r: ErrorReason) = HavocallFailed(offendingNode, r, cached)
  }

  def HavocallFailed(offendingNode: Quasihavocall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => HavocallFailed(offendingNode, reason))


  case class HeuristicsFailed(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "heuristics.failed"
    val text = "Applying heuristics failed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = HeuristicsFailed(offendingNode, this.reason, this.cached)
    def withReason(r: ErrorReason) = HeuristicsFailed(offendingNode, r, cached)
  }

  def HeuristicsFailed(offendingNode: ErrorNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => HeuristicsFailed(offendingNode, reason))

  case class VerificationErrorWithCounterexample(ve: AbstractVerificationError, model: String, symState: String, currentMember: String, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = ve.id
    val text = null // not used since readableMessage is overridden

    override def readableMessage(withId: Boolean, withPosition: Boolean = false): String = ve.readableMessage(withId, withPosition)

    override def offendingNode = ve.offendingNode

    override def reason = ve.reason

    def withNode(offendingNode: errors.ErrorNode) =
      VerificationErrorWithCounterexample(ve.withNode(offendingNode).asInstanceOf[AbstractVerificationError], model, symState, currentMember, cached)

    def withReason(r: ErrorReason) = VerificationErrorWithCounterexample(ve.withReason(r), model, symState, currentMember, cached)
  }
}

object reasons {
  type ErrorNode = errors.ErrorNode

  case class InternalReason(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "internal"
    val readableMessage = explanation

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InternalReason(offendingNode, this.explanation)
  }

  case class FeatureUnsupported(offendingNode: ErrorNode, explanation: String) extends AbstractErrorReason {
    val id = "feature.unsupported"
    def readableMessage = s"$offendingNode is not supported. $explanation"

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FeatureUnsupported(offendingNode, this.explanation)
  }

  case class UnexpectedNode(offendingNode: ErrorNode, explanation: String, stackTrace: Seq[StackTraceElement])
      extends AbstractErrorReason {

    val id = "unexpected.node"
    def readableMessage = s"$offendingNode occurred unexpectedly. $explanation"

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = UnexpectedNode(offendingNode, this.explanation, this.stackTrace)
  }

  case class AssertionFalse(offendingNode: Exp) extends AbstractErrorReason {
    val id = "assertion.false"
    def readableMessage = s"Assertion $offendingNode might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = AssertionFalse(offendingNode.asInstanceOf[Exp])
  }

  // Note: this class should be deprecated/removed - we no longer support epsilon permissions in the language
  case class EpsilonAsParam(offendingNode: Exp) extends AbstractErrorReason {
    val id = "epsilon.as.param"
    def readableMessage = s"The parameter $offendingNode might be an epsilon permission, which is not allowed for method parameters."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = EpsilonAsParam(offendingNode.asInstanceOf[Exp])
  }

  case class ReceiverNull(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "receiver.null"
    def readableMessage = s"Receiver of $offendingNode might be null."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ReceiverNull(offendingNode.asInstanceOf[LocationAccess])
  }

  case class DivisionByZero(offendingNode: Exp) extends AbstractErrorReason {
    val id = "division.by.zero"
    def readableMessage = s"Divisor $offendingNode might be zero."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = DivisionByZero(offendingNode.asInstanceOf[Exp])
  }

  case class NegativePermission(offendingNode: Exp) extends AbstractErrorReason {
    val id = "negative.permission"
    def readableMessage = s"Fraction $offendingNode might be negative."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = NegativePermission(offendingNode.asInstanceOf[Exp])
  }

  case class NonPositivePermission(offendingNode: Exp) extends AbstractErrorReason {
    val id = "permission.not.positive"

    def readableMessage = s"Fraction $offendingNode might not be positive."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = NonPositivePermission(offendingNode.asInstanceOf[Exp])
  }

  case class InsufficientPermission(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "insufficient.permission"
    def readableMessage = s"There might be insufficient permission to access $offendingNode"

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InsufficientPermission(offendingNode.asInstanceOf[LocationAccess])
  }

  case class InvalidPermMultiplication(offendingNode: PermMul) extends AbstractErrorReason {
    val id = "invalid.perm.multiplication"
    def readableMessage = s"Permission multiplication might not be possible, as an operand might contain epsilons."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InvalidPermMultiplication(offendingNode.asInstanceOf[PermMul])
  }

  case class MagicWandChunkNotFound(offendingNode: MagicWand) extends AbstractErrorReason {
    val id = "wand.not.found"
    def readableMessage = s"Magic wand instance not found."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = MagicWandChunkNotFound(offendingNode.asInstanceOf[MagicWand])
  }

  case class QPAssertionNotInjective(offendingNode: ResourceAccess) extends AbstractErrorReason {
    val id = "qp.not.injective"
    def readableMessage = s"Quantified resource $offendingNode might not be injective."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = QPAssertionNotInjective(offendingNode.asInstanceOf[ResourceAccess])
  }

  case class QuasihavocallNotInjective(offendingNode: Quasihavocall) extends AbstractErrorReason {
    val id = "quasihavocall.not.injective"
    val readableMessage = s"Quasihavocall statement $offendingNode might not be injective."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = QuasihavocallNotInjective(offendingNode.asInstanceOf[Quasihavocall])
  }

  case class LabelledStateNotReached(offendingNode: LabelledOld) extends AbstractErrorReason {
    val id = "labelled.state.not.reached"
    val lbl = offendingNode.oldLabel
    def readableMessage = s"Did not reach labelled state $lbl required to evaluate $offendingNode."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LabelledStateNotReached(offendingNode.asInstanceOf[LabelledOld])
  }

  case class SeqIndexNegative(seq: Exp, offendingNode: Exp) extends AbstractErrorReason {
    val id = "seq.index.negative"
    def readableMessage = s"Index $offendingNode into $seq might be negative."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
      SeqIndexNegative(seq, offendingNode.asInstanceOf[Exp])
  }

  case class SeqIndexExceedsLength(seq: Exp, offendingNode: Exp) extends AbstractErrorReason {
    val id = "seq.index.length"
    def readableMessage = s"Index $offendingNode into $seq might exceed sequence length."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
      SeqIndexExceedsLength(seq, offendingNode.asInstanceOf[Exp])
  }

  case class MapKeyNotContained(map: Exp, offendingNode: Exp) extends AbstractErrorReason {
    val id = "map.key.contains"
    def readableMessage = s"Map $map might not contain an entry at key $offendingNode."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
      MapKeyNotContained(map, offendingNode.asInstanceOf[Exp])
  }
}
