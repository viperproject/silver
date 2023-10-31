// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.verifier.{AbstractVerificationError, ErrorMessage, ErrorReason, ExtensionAbstractVerificationError}
import viper.silver.verifier.reasons.ErrorNode

sealed abstract class PredicateInstanceError extends ExtensionAbstractVerificationError

case class PredicateInstanceNoAccess(override val offendingNode: ErrorNode, override val reason: ErrorReason, override val cached: Boolean) extends PredicateInstanceError {
  override protected def text: String = "Accessing predicate instance might fail."

  override def withReason(reason: ErrorReason): AbstractVerificationError = PredicateInstanceNoAccess(this.offendingNode, this.reason, cached)

  override def id: String = "predicateinstance.no.access"

  override def withNode(offendingNode: ErrorNode): ErrorMessage = PredicateInstanceNoAccess(offendingNode, this.reason, cached)
}


