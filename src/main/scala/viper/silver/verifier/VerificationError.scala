// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.verifier

import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Rewritable

trait ErrorMessage {
  def id: String
  def offendingNode: errors.ErrorNode
  def pos: Position
  def readableMessage: String

  // Should consider refactoring as a transformer, if/once we make the error message structure recursive
  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) : ErrorMessage
}

trait VerificationError extends AbstractError with ErrorMessage {
  def reason: ErrorReason
  def readableMessage(withId: Boolean = false, withPosition: Boolean = false): String
  override def readableMessage = readableMessage(false, true)
  def loggableMessage = s"$fullId-$pos"
  def fullId = s"$id:${reason.id}"
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

trait ErrorReason extends ErrorMessage

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
  def f = x => null
}

abstract class AbstractVerificationError extends VerificationError {
  protected def text: String

  def pos = offendingNode.pos

  def readableMessage(withId: Boolean, withPosition: Boolean) = {
    val idStr = if (withId) s"[$fullId] " else ""
    val posStr = if (withPosition) s" ($pos)" else ""

    s"$idStr$text ${reason.readableMessage}$posStr"
  }

  /** Transform the error back according to the specified error transformations */
  def transformedError(): AbstractVerificationError = {
    val errorT = offendingNode.transformError(this)
    val reasonT = errorT.reason.offendingNode.transformReason(errorT.reason)

    errorT.withReason(reasonT)
  }

  def withReason(reason: ErrorReason): AbstractVerificationError

  override def toString = readableMessage(true, true)
}

abstract class AbstractErrorReason extends ErrorReason {
  def pos = offendingNode.pos
  override def toString = readableMessage
}

object errors {
  type ErrorNode = Node with Positioned with TransformableErrors with Rewritable

  case class Internal(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = Internal(offendingNode, this.reason)
    def withReason(r: ErrorReason) = Internal(offendingNode, r)
  }
  // internal errors can be created with dummy nodes
  def Internal(reason: ErrorReason) : Internal = Internal(DummyNode, reason)
  def Internal(offendingNode: ErrorNode = DummyNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => Internal(offendingNode, reason))

  case class AssignmentFailed(offendingNode: AbstractAssign, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "assignment.failed"
    val text = "Assignment might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = AssignmentFailed(offendingNode.asInstanceOf[AbstractAssign], this.reason)
    def withReason(r: ErrorReason) = AssignmentFailed(offendingNode, r)
  }

  def AssignmentFailed(offendingNode: AbstractAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssignmentFailed(offendingNode, reason))

  case class CallFailed(offendingNode: MethodCall, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "call.failed"
    val text = "Method call might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = CallFailed(offendingNode.asInstanceOf[MethodCall], this.reason)
    def withReason(r: ErrorReason) = CallFailed(offendingNode, r)
  }

  def CallFailed(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => CallFailed(offendingNode, reason))

  case class ContractNotWellformed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "not.wellformed"
    val text = s"Contract might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ContractNotWellformed(offendingNode.asInstanceOf[Exp], this.reason)
    def withReason(r: ErrorReason) = ContractNotWellformed(offendingNode, r)
  }

  def ContractNotWellformed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ContractNotWellformed(offendingNode, reason))

  case class PreconditionInCallFalse(offendingNode: MethodCall, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "call.precondition"
    val text = s"The precondition of method ${offendingNode.methodName} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PreconditionInCallFalse(offendingNode.asInstanceOf[MethodCall], this.reason)
    def withReason(r: ErrorReason) = PreconditionInCallFalse(offendingNode, r)
  }

  def PreconditionInCallFalse(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInCallFalse(offendingNode, reason))

  case class PreconditionInAppFalse(offendingNode: FuncApp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "application.precondition"
    val text = s"Precondition of function ${offendingNode.funcname} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PreconditionInAppFalse(offendingNode.asInstanceOf[FuncApp], this.reason)
    def withReason(r: ErrorReason) = PreconditionInAppFalse(offendingNode, r)
  }

  def PreconditionInAppFalse(offendingNode: FuncApp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInAppFalse(offendingNode, reason))

  case class ExhaleFailed(offendingNode: Exhale, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "exhale.failed"
    val text = "Exhale might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ExhaleFailed(offendingNode.asInstanceOf[Exhale], this.reason)
    def withReason(r: ErrorReason) = ExhaleFailed(offendingNode, r)
  }

  def ExhaleFailed(offendingNode: Exhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ExhaleFailed(offendingNode, reason))

  case class InhaleFailed(offendingNode: Inhale, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "inhale.failed"
    val text = "Inhale might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = InhaleFailed(offendingNode.asInstanceOf[Inhale], this.reason)
    def withReason(r: ErrorReason) = InhaleFailed(offendingNode, r)
  }

  def InhaleFailed(offendingNode: Inhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => InhaleFailed(offendingNode, reason))

  case class IfFailed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "if.failed"
    val text = "Conditional statement might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = IfFailed(offendingNode.asInstanceOf[Exp], this.reason)
    def withReason(r: ErrorReason) = IfFailed(offendingNode, r)
  }

  def IfFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => IfFailed(offendingNode, reason))

  case class WhileFailed(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "while.failed"
    val text = "While statement might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = WhileFailed(offendingNode.asInstanceOf[Exp], this.reason)
    def withReason(r: ErrorReason) = WhileFailed(offendingNode, r)
  }

  def WhileFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => WhileFailed(offendingNode, reason))

  case class AssertFailed(offendingNode: Assert, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "assert.failed"
    val text = "Assert might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = AssertFailed(offendingNode.asInstanceOf[Assert], this.reason)
    def withReason(r: ErrorReason) = AssertFailed(offendingNode, r)
  }

  def AssertFailed(offendingNode: Assert): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertFailed(offendingNode, reason))

  case class TerminationFailed(offendingNode: Function, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "termination.failed"
    val text = s"Function ${offendingNode.name} might not terminate."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationFailed(offendingNode.asInstanceOf[Function], this.reason)
    def withReason(r: ErrorReason) = TerminationFailed(offendingNode, r)
  }

  def TerminationFailed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((r: ErrorReason) => TerminationFailed(offendingNode, r))

  case class PostconditionViolated(offendingNode: Exp, member: Contracted, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "postcondition.violated"
    val text = s"Postcondition of ${member.name} might not hold."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PostconditionViolated(offendingNode.asInstanceOf[Exp], this.member, this.reason)
    def withReason(r: ErrorReason) = PostconditionViolated(offendingNode, member, r)
  }

  def PostconditionViolated(offendingNode: Exp, member: Contracted): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, member, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FoldFailed(offendingNode.asInstanceOf[Fold], this.reason)
    def withReason(r: ErrorReason) = FoldFailed(offendingNode, r)
  }

  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = UnfoldFailed(offendingNode.asInstanceOf[Unfold], this.reason)
    def withReason(r: ErrorReason) = UnfoldFailed(offendingNode, r)
  }

  def UnfoldFailed(offendingNode: Unfold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnfoldFailed(offendingNode, reason))

  case class PackageFailed(offendingNode: Package, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "package.failed"
    val text = s"Packaging wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PackageFailed(offendingNode.asInstanceOf[Package], this.reason)
    def withReason(r: ErrorReason) = PackageFailed(offendingNode, r)
  }

  def PackageFailed(offendingNode: Package): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PackageFailed(offendingNode, reason))

  case class ApplyFailed(offendingNode: Apply, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "apply.failed"
    val text = s"Applying wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ApplyFailed(offendingNode.asInstanceOf[Apply], this.reason)
    def withReason(r: ErrorReason) = ApplyFailed(offendingNode, r)
  }

  def ApplyFailed(offendingNode: Apply): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ApplyFailed(offendingNode, reason))

  case class LoopInvariantNotPreserved(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "invariant.not.preserved"
    val text = s"Loop invariant $offendingNode might not be preserved."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LoopInvariantNotPreserved(offendingNode.asInstanceOf[Exp], this.reason)
    def withReason(r: ErrorReason) = LoopInvariantNotPreserved(offendingNode, r)
  }

  def LoopInvariantNotPreserved(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotPreserved(offendingNode, reason))

  case class LoopInvariantNotEstablished(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "invariant.not.established"
    val text = s"Loop invariant $offendingNode might not hold on entry."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LoopInvariantNotEstablished(offendingNode.asInstanceOf[Exp], this.reason)
    def withReason(r: ErrorReason) = LoopInvariantNotEstablished(offendingNode, r)
  }

  def LoopInvariantNotEstablished(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotEstablished(offendingNode, reason))

  case class FunctionNotWellformed(offendingNode: Function, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "function.not.wellformed"
    val text = s"Function might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FunctionNotWellformed(offendingNode.asInstanceOf[Function], this.reason)
    def withReason(r: ErrorReason) = FunctionNotWellformed(offendingNode, r)
  }

  def FunctionNotWellformed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FunctionNotWellformed(offendingNode, reason))

  case class PredicateNotWellformed(offendingNode: Predicate, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "predicate.not.wellformed"
    val text = s"Predicate might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = PredicateNotWellformed(offendingNode.asInstanceOf[Predicate], this.reason)
    def withReason(r: ErrorReason) = PredicateNotWellformed(offendingNode, r)
  }

  def PredicateNotWellformed(offendingNode: Predicate): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PredicateNotWellformed(offendingNode, reason))

  case class MagicWandNotWellformed(offendingNode: MagicWand, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "wand.not.wellformed"
    val text = s"Magic wand might not be well-formed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = MagicWandNotWellformed(offendingNode.asInstanceOf[MagicWand], this.reason)
    def withReason(r: ErrorReason) = MagicWandNotWellformed(offendingNode, r)
  }

  def MagicWandNotWellformed(offendingNode: MagicWand): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => MagicWandNotWellformed(offendingNode, reason))

  case class LetWandFailed(offendingNode: LocalVarAssign, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "letwand.failed"
    val text = s"Referencing a wand might fail."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = LetWandFailed(offendingNode.asInstanceOf[LocalVarAssign], this.reason)
    def withReason(r: ErrorReason) = LetWandFailed(offendingNode, r)
  }

  def LetWandFailed(offendingNode: LocalVarAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LetWandFailed(offendingNode, reason))

  case class HeuristicsFailed(offendingNode: ErrorNode, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "heuristics.failed"
    val text = "Applying heuristics failed."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = HeuristicsFailed(offendingNode, this.reason)
    def withReason(r: ErrorReason) = HeuristicsFailed(offendingNode, r)
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
      VerificationErrorWithCounterexample(ve.withNode(offendingNode).asInstanceOf[AbstractVerificationError], model, symState, currentMember)

    def withReason(r: ErrorReason) = VerificationErrorWithCounterexample(ve.withReason(r), model, symState, currentMember)
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

  case class InsufficientPermission(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "insufficient.permission"
    def readableMessage = s"There might be insufficient permission to access $offendingNode."

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

  case class ReceiverNotInjective(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "receiver.not.injective"
    def readableMessage = s"Receiver of $offendingNode [$pos]  might not be injective."

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = ReceiverNotInjective(offendingNode.asInstanceOf[LocationAccess])
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
}
