// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.ast.utility.Consistency

/**
 * A name generator for Viper.
 */
class SilNameGenerator extends DefaultNameGenerator {
  val identFirstLetter = "[a-zA-Z$_]"
  val identOtherLetterChars = "a-zA-Z0-9$_'"
  val identOtherLetter = s"[$identOtherLetterChars]"
  val reservedNames = Consistency.reservedNames.toSet
  val separator = "_"
  val firstCharacter = identFirstLetter.r
  val otherCharacter = identOtherLetter.r

  override def createIdentifier(input: String) = {
    super.createIdentifier(input)
  } ensuring {
    Consistency.validIdentifier _
  }

}
