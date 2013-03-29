package semper.sil.utility

import semper.sil.parser.Parser

/**
 * A name generator for SIL.
 *
 * @author Stefan Heule
 */
class SilNameGenerator extends NameGenerator {

  def separator = "_"
  def firstCharacter = Parser.identFirstLetter.r
  def otherCharacter = Parser.identOtherLetter.r

}
