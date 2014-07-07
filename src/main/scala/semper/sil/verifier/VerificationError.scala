/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.sil.verifier

import semper.sil.ast._

trait ErrorMessage {
  type PositionedNode = Node with Positioned
  def id: String
  def offendingNode: PositionedNode
  def pos: Position
  def readableMessage: String
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
  }

  def dueTo(reason: ErrorReason) = f(reason)

  override lazy val toString = f(DummyReason).readableMessage(true, true)
}

object PartialVerificationError {
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
  }

  def Internal(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => Internal(offendingNode, reason))

  case class AssignmentFailed(offendingNode: AbstractAssign, reason: ErrorReason) extends AbstractVerificationError {
    val id = "assignment.failed"
    val text = "Assignment might fail."
  }

  def AssignmentFailed(offendingNode: AbstractAssign): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssignmentFailed(offendingNode, reason))

  case class CallFailed(offendingNode: MethodCall, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.failed"
    val text = "Method call might fail."
  }

  def CallFailed(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => CallFailed(offendingNode, reason))

  case class ContractNotWellformed(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "not.wellformed"
    val text = s"Contract might not be well-formed."
  }

  def ContractNotWellformed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ContractNotWellformed(offendingNode, reason))

  case class PreconditionInCallFalse(offendingNode: MethodCall, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.precondition"
    val text = s"The precondition of method ${offendingNode.methodName} might not hold."
  }

  def PreconditionInCallFalse(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInCallFalse(offendingNode, reason))

  case class PreconditionInAppFalse(offendingNode: FuncApp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "application.precondition"
    val text = s"Precondition of function ${offendingNode.funcname} might not hold."
  }

  def PreconditionInAppFalse(offendingNode: FuncApp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PreconditionInAppFalse(offendingNode, reason))

  case class ExhaleFailed(offendingNode: Exhale, reason: ErrorReason) extends AbstractVerificationError {
    val id = "exhale.failed"
    val text = "Exhale might fail."
  }

  def ExhaleFailed(offendingNode: Exhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ExhaleFailed(offendingNode, reason))

  case class InhaleFailed(offendingNode: Inhale, reason: ErrorReason) extends AbstractVerificationError {
    val id = "inhale.failed"
    val text = "Inhale might fail."
  }

  def InhaleFailed(offendingNode: Inhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => InhaleFailed(offendingNode, reason))

  case class IfFailed(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "if.failed"
    val text = "Conditional statement might fail."
  }

  def IfFailed(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => IfFailed(offendingNode, reason))

  case class WhileFailed(offendingNode: While, reason: ErrorReason) extends AbstractVerificationError {
    val id = "while.failed"
    val text = "While statement might fail."
  }

  def WhileFailed(offendingNode: While): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => WhileFailed(offendingNode, reason))

  case class AssertFailed(offendingNode: Assert, reason: ErrorReason) extends AbstractVerificationError {
    val id = "assert.failed"
    val text = "Assert might fail."
  }

  def AssertFailed(offendingNode: Assert): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertFailed(offendingNode, reason))

  case class PostconditionViolated(offendingNode: Exp, member: Contracted, reason: ErrorReason) extends AbstractVerificationError {
    val id = "postcondition.violated"
    val text = s"Postcondition of ${member.name} might not hold."
  }

  def PostconditionViolated(offendingNode: Exp, member: Contracted): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, member, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} might fail."
  }

  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} might fail."
  }

  def UnfoldFailed(offendingNode: Unfold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnfoldFailed(offendingNode, reason))

  case class LoopInvariantNotPreserved(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "invariant.not.preserved"
    val text = s"Loop invariant $offendingNode might not be preserved."
  }

  def LoopInvariantNotPreserved(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotPreserved(offendingNode, reason))

  case class LoopInvariantNotEstablished(offendingNode: Exp, reason: ErrorReason) extends AbstractVerificationError {
    val id = "invariant.not.established"
    val text = s"Loop invariant $offendingNode might not hold on entry."
  }

  def LoopInvariantNotEstablished(offendingNode: Exp): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotEstablished(offendingNode, reason))

  case class FunctionNotWellformed(offendingNode: Function, reason: ErrorReason) extends AbstractVerificationError {
    val id = "function.not.wellformed"
    val text = s"Function might not be well-formed."
  }

  def FunctionNotWellformed(offendingNode: Function): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FunctionNotWellformed(offendingNode, reason))

  case class PredicateNotWellformed(offendingNode: Predicate, reason: ErrorReason) extends AbstractVerificationError {
    val id = "predicate.not.wellformed"
    val text = s"Predicate might not be well-formed."
  }

  def PredicateNotWellformed(offendingNode: Predicate): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PredicateNotWellformed(offendingNode, reason))
}

object reasons {
  type PositionedNode = Node with Positioned

  case class FeatureUnsupported(offendingNode: PositionedNode, explanation: String) extends AbstractErrorReason {
    val id = "feature.unsupported"
    def readableMessage = s"$offendingNode is not supported. $explanation"
  }

  case class UnexpectedNode(offendingNode: PositionedNode, explanation: String, stackTrace: Seq[StackTraceElement])
      extends AbstractErrorReason {

    val id = "unexpected.node"
    def readableMessage = s"$offendingNode occurred unexpectedly. $explanation"
  }

  case class AssertionFalse(offendingNode: Exp) extends AbstractErrorReason {
    val id = "assertion.false"
    def readableMessage = s"Assertion $offendingNode might not hold."
  }

  case class EpsilonAsParam(offendingNode: Exp) extends AbstractErrorReason {
    val id = "epsilon.as.param"
    def readableMessage = s"The parameter $offendingNode might be an epsilon permission, which is not allowed for method parameters."
  }

  case class ReceiverNull(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "receiver.null"
    def readableMessage = s"Receiver of $offendingNode might be null."
  }

  case class DivisionByZero(offendingNode: Exp) extends AbstractErrorReason {
    val id = "division.by.zero"
    def readableMessage = s"Divisor $offendingNode might be zero."
  }

  case class NonPositivePermission(offendingNode: Exp) extends AbstractErrorReason {
    val id = "non.positive.permission"
    def readableMessage = s"Fraction $offendingNode might not be positive."
  }

  case class InsufficientPermission(offendingNode: LocationAccess) extends AbstractErrorReason {
    val id = "insufficient.permission"
    def readableMessage = s"There might be insufficient permission to access $offendingNode."
  }

  case class InvalidPermMultiplication(offendingNode: PermMul) extends AbstractErrorReason {
    val id = "invalid.perm.multiplication"
    def readableMessage = s"Permission multiplication might not be possible, as an operand might contain epsilons."
  }
}
