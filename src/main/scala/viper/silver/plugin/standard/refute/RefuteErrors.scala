// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import viper.silver.verifier._

sealed abstract class RefuteError extends ExtensionAbstractVerificationError
sealed abstract class RefuteErrorReason extends ExtensionAbstractErrorReason

case class RefuteFailed(override val offendingNode: Refute, override val reason: ErrorReason, override val cached: Boolean = false) extends RefuteError {
  override val id = "refute.failed"
  override val text = "Refute holds in all cases or could not be reached (e.g. see Silicon `numberOfErrorsToReport`)."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): RefuteFailed =
    RefuteFailed(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason): RefuteFailed = RefuteFailed(offendingNode, r, cached)
}

case class RefutationTrue(offendingNode: reasons.ErrorNode) extends RefuteErrorReason {
  override val id: String = "refutation.true"

  override val readableMessage: String = s"Assertion $offendingNode definitely holds."

  override def withNode(offendingNode: reasons.ErrorNode): ErrorMessage = RefutationTrue(offendingNode)
}
