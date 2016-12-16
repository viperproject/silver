/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.verifier

import viper.silver.ast._

trait ErrorMessage {
  def id: String
  def offendingNode: errors.PositionedNode
  def pos: Position
  def readableMessage: String

  // Should consider refactoring as a transformer, if/once we make the error message structure recursive
  def withNode(offendingNode: errors.PositionedNode = this.offendingNode) : ErrorMessage
}

trait VerificationError extends AbstractError with ErrorMessage {
  def reason: ErrorReason
  def readableMessage(withId: Boolean = false, withPosition: Boolean = true): String
  override def readableMessage = readableMessage(false, true)
  def fullId = s"$id:${reason.id}"
}

trait ErrorReason extends ErrorMessage

trait PartialVerificationError {
  def f: ErrorReason => VerificationError

  private object DummyReason extends AbstractErrorReason {
    val id = "?"
    val readableMessage = "?"

    val offendingNode = new Node with Positioned {
      val pos = NoPosition
    }

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = DummyReason
  }

  def dueTo(reason: ErrorReason) = f(reason)

  // apply a transformation to the node attached to the eventually-supplied error reason (note: not currently to other parameters, nor to the node attached to the error itself)
  def withReasonNodeTransformed(t : errors.PositionedNode => errors.PositionedNode) = PartialVerificationError((r:ErrorReason) => f(r.withNode(t(r.offendingNode)).asInstanceOf[ErrorReason]))

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

  override def toString = readableMessage(true, true)
}

abstract class AbstractErrorReason extends ErrorReason {
  def pos = offendingNode.pos
  override def toString = readableMessage
}

object errors {
  type PositionedNode = Node with Positioned

  case class Internal(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = Internal(offendingNode, this.reason)
  }

  def Internal(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => Internal(offendingNode, reason))

  case class AssignmentFailed(offendingNode: AbstractAssign, reason: ErrorReason) extends AbstractVerificationError {
    val id = "assignment.failed"
    val text = "Assignment might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = AssignmentFailed(offendingNode.asInstanceOf[AbstractAssign], this.reason)
  }

  def AssignmentFailed(offendingNode: AbstractAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssignmentFailed(offendingNode, reason))

  case class CallFailed(offendingNode: MethodCall, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.failed"
    val text = "Method call might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = CallFailed(offendingNode.asInstanceOf[MethodCall], this.reason)
  }

  def CallFailed(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => CallFailed(offendingNode, reason))

  case class ContractNotWellformed(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "not.wellformed"
    val text = s"Contract might not be well-formed."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = ContractNotWellformed(offendingNode.asInstanceOf[Exp], this.reason)
  }

  def ContractNotWellformed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ContractNotWellformed(offendingNode, reason))

  case class PreconditionInCallFalse(offendingNode: MethodCall, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.precondition"
    val text = s"The precondition of method ${offendingNode.methodName} might not hold."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = PreconditionInCallFalse(offendingNode.asInstanceOf[MethodCall], this.reason)
  }

  def PreconditionInCallFalse(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInCallFalse(offendingNode, reason))

  case class PreconditionInAppFalse(offendingNode: FuncApp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "application.precondition"
    val text = s"Precondition of function ${offendingNode.funcname} might not hold."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = PreconditionInAppFalse(offendingNode.asInstanceOf[FuncApp], this.reason)
  }

  def PreconditionInAppFalse(offendingNode: FuncApp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInAppFalse(offendingNode, reason))

  case class ExhaleFailed(offendingNode: Exhale, reason: ErrorReason) extends AbstractVerificationError {
    val id = "exhale.failed"
    val text = "Exhale might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = ExhaleFailed(offendingNode.asInstanceOf[Exhale], this.reason)
  }

  def ExhaleFailed(offendingNode: Exhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ExhaleFailed(offendingNode, reason))

  case class InhaleFailed(offendingNode: Inhale, reason: ErrorReason) extends AbstractVerificationError {
    val id = "inhale.failed"
    val text = "Inhale might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = InhaleFailed(offendingNode.asInstanceOf[Inhale], this.reason)
  }

  def InhaleFailed(offendingNode: Inhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => InhaleFailed(offendingNode, reason))

  case class IfFailed(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "if.failed"
    val text = "Conditional statement might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = IfFailed(offendingNode.asInstanceOf[Exp], this.reason)
  }

  def IfFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => IfFailed(offendingNode, reason))

  case class WhileFailed(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "while.failed"
    val text = "While statement might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = WhileFailed(offendingNode.asInstanceOf[Exp], this.reason)
  }

  def WhileFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => WhileFailed(offendingNode, reason))

  case class AssertFailed(offendingNode: Assert, reason: ErrorReason) extends AbstractVerificationError {
    val id = "assert.failed"
    val text = "Assert might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = AssertFailed(offendingNode.asInstanceOf[Assert], this.reason)
  }

  def AssertFailed(offendingNode: Assert): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertFailed(offendingNode, reason))

  case class PostconditionViolated(offendingNode: Exp, member: Contracted, reason: ErrorReason) extends AbstractVerificationError {
    val id = "postcondition.violated"
    val text = s"Postcondition of ${member.name} might not hold."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = PostconditionViolated(offendingNode.asInstanceOf[Exp], this.member, this.reason)
  }

  def PostconditionViolated(offendingNode: Exp, member: Contracted): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, member, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = FoldFailed(offendingNode.asInstanceOf[Fold], this.reason)
  }

  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = UnfoldFailed(offendingNode.asInstanceOf[Unfold], this.reason)
  }

  def UnfoldFailed(offendingNode: Unfold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnfoldFailed(offendingNode, reason))

  case class PackageFailed(offendingNode: Package, reason: ErrorReason) extends AbstractVerificationError {
    val id = "package.failed"
    val text = s"Packaging wand might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = PackageFailed(offendingNode.asInstanceOf[Package], this.reason)
  }

  def PackageFailed(offendingNode: Package): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PackageFailed(offendingNode, reason))

  case class ApplyFailed(offendingNode: Apply, reason: ErrorReason) extends AbstractVerificationError {
    val id = "apply.failed"
    val text = s"Applying wand might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = ApplyFailed(offendingNode.asInstanceOf[Apply], this.reason)
  }

  def ApplyFailed(offendingNode: Apply): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ApplyFailed(offendingNode, reason))

  case class LoopInvariantNotPreserved(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "invariant.not.preserved"
    val text = s"Loop invariant $offendingNode might not be preserved."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = LoopInvariantNotPreserved(offendingNode.asInstanceOf[Exp], this.reason)
  }

  def LoopInvariantNotPreserved(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotPreserved(offendingNode, reason))

  case class LoopInvariantNotEstablished(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "invariant.not.established"
    val text = s"Loop invariant $offendingNode might not hold on entry."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = LoopInvariantNotEstablished(offendingNode.asInstanceOf[Exp], this.reason)
  }

  def LoopInvariantNotEstablished(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotEstablished(offendingNode, reason))

  case class FunctionNotWellformed(offendingNode: Function, reason: ErrorReason) extends AbstractVerificationError {
    val id = "function.not.wellformed"
    val text = s"Function might not be well-formed."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = FunctionNotWellformed(offendingNode.asInstanceOf[Function], this.reason)
  }

  def FunctionNotWellformed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FunctionNotWellformed(offendingNode, reason))

  case class PredicateNotWellformed(offendingNode: Predicate, reason: ErrorReason) extends AbstractVerificationError {
    val id = "predicate.not.wellformed"
    val text = s"Predicate might not be well-formed."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = PredicateNotWellformed(offendingNode.asInstanceOf[Predicate], this.reason)
  }

  def PredicateNotWellformed(offendingNode: Predicate): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PredicateNotWellformed(offendingNode, reason))

  case class MagicWandNotWellformed(offendingNode: MagicWand, reason: ErrorReason) extends AbstractVerificationError {
    val id = "wand.not.wellformed"
    val text = s"Magic wand might not be well-formed."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = MagicWandNotWellformed(offendingNode.asInstanceOf[MagicWand], this.reason)
  }

  def MagicWandNotWellformed(offendingNode: MagicWand): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => MagicWandNotWellformed(offendingNode, reason))

  case class LetWandFailed(offendingNode: LocalVarAssign, reason: ErrorReason) extends AbstractVerificationError {
    val id = "letwand.failed"
    val text = s"Referencing a wand might fail."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = LetWandFailed(offendingNode.asInstanceOf[LocalVarAssign], this.reason)
  }

  def LetWandFailed(offendingNode: LocalVarAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LetWandFailed(offendingNode, reason))

  case class HeuristicsFailed(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "heuristics.failed"
    val text = "Applying heuristics failed."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = HeuristicsFailed(offendingNode, this.reason)
  }

  def HeuristicsFailed(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => HeuristicsFailed(offendingNode, reason))
}

object reasons {
  type PositionedNode = errors.PositionedNode

  case class InternalReason(offendingNode: PositionedNode, explanation: String) extends AbstractErrorReason {
    val id = "internal"
    val readableMessage = explanation

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = InternalReason(offendingNode, this.explanation)
  }

  case class FeatureUnsupported(offendingNode: PositionedNode, explanation: String) extends AbstractErrorReason {
    val id = "feature.unsupported"
    def readableMessage = s"$offendingNode is not supported. $explanation"

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = FeatureUnsupported(offendingNode, this.explanation)
  }

  case class UnexpectedNode(offendingNode: PositionedNode, explanation: String, stackTrace: Seq[StackTraceElement])
      extends AbstractErrorReason {

    val id = "unexpected.node"
    def readableMessage = s"$offendingNode occurred unexpectedly. $explanation"

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = UnexpectedNode(offendingNode, this.explanation, this.stackTrace)
  }

  case class AssertionFalse(offendingNode: Exp) extends AbstractErrorReason {
    val id = "assertion.false"
    def readableMessage = s"Assertion $offendingNode might not hold."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = AssertionFalse(offendingNode.asInstanceOf[Exp])
  }

  // Note: this class should be deprecated/removed - we no longer support epsilon permissions in the language
  case class EpsilonAsParam(offendingNode: Exp) extends AbstractErrorReason {
    val id = "epsilon.as.param"
    def readableMessage = s"The parameter $offendingNode might be an epsilon permission, which is not allowed for method parameters."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = EpsilonAsParam(offendingNode.asInstanceOf[Exp])
  }

  case class ReceiverNull(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "receiver.null"
    def readableMessage = s"Receiver of $offendingNode might be null."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = ReceiverNull(offendingNode.asInstanceOf[LocationAccess])
  }

  case class DivisionByZero(offendingNode: Exp) extends AbstractErrorReason {
    val id = "division.by.zero"
    def readableMessage = s"Divisor $offendingNode might be zero."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = DivisionByZero(offendingNode.asInstanceOf[Exp])
  }

  case class NegativePermission(offendingNode: Exp) extends AbstractErrorReason {
    val id = "negative.permission"
    def readableMessage = s"Fraction $offendingNode might be negative."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = NegativePermission(offendingNode.asInstanceOf[Exp])
  }

  case class InsufficientPermission(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "insufficient.permission"
    def readableMessage = s"There might be insufficient permission to access $offendingNode."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = InsufficientPermission(offendingNode.asInstanceOf[LocationAccess])
  }

  case class InvalidPermMultiplication(offendingNode: PermMul) extends AbstractErrorReason {
    val id = "invalid.perm.multiplication"
    def readableMessage = s"Permission multiplication might not be possible, as an operand might contain epsilons."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = InvalidPermMultiplication(offendingNode.asInstanceOf[PermMul])
  }

  case class MagicWandChunkNotFound(offendingNode: MagicWand) extends AbstractErrorReason {
    val id = "wand.not.found"
    def readableMessage = s"Magic wand instance not found."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = MagicWandChunkNotFound(offendingNode.asInstanceOf[MagicWand])
  }

  case class NamedMagicWandChunkNotFound(offendingNode: AbstractLocalVar) extends AbstractErrorReason {
    val id = "wand.not.found"
    def readableMessage = s"Magic wand instance not found."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = NamedMagicWandChunkNotFound(offendingNode.asInstanceOf[AbstractLocalVar])
  }

  // AS: not sure why/if we need this as a special case
  case class MagicWandChunkOutdated(offendingNode: MagicWand) extends AbstractErrorReason {
    val id = "wand.outdated"
    def readableMessage = s"Found magic wand instance, but now-expressions might not match."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = MagicWandChunkOutdated(offendingNode.asInstanceOf[MagicWand])
  }

  case class ReceiverNotInjective(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "receiver.not.injective"
    def readableMessage = s"Receiver of $offendingNode [$pos]  might not be injective."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = ReceiverNotInjective(offendingNode.asInstanceOf[LocationAccess])
  }

  case class LabelledStateNotReached(offendingNode: LabelledOld) extends AbstractErrorReason {
    val id = "labelled.state.not.reached"
    val lbl = offendingNode.oldLabel
    def readableMessage = s"Did not reach labelled state $lbl required to evaluate $offendingNode."

    def withNode(offendingNode: errors.PositionedNode = this.offendingNode) = LabelledStateNotReached(offendingNode.asInstanceOf[LabelledOld])
  }
}
