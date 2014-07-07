/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.sil.utility

import semper.sil.parser.Parser
import semper.sil.ast.utility.Consistency

/**
 * A name generator for SIL.
 *
 * @author Stefan Heule
 */
class SilNameGenerator extends DefaultNameGenerator {

  val reservedNames = Consistency.reservedNames.toSet
  val separator = "_"
  val firstCharacter = Parser.identFirstLetter.r
  val otherCharacter = Parser.identOtherLetter.r

  override def createIdentifier(input: String) = {
    super.createIdentifier(input)
  } ensuring {
    Consistency.validIdentifier(_)
  }

}
