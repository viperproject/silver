package semper.sil.utility

import semper.sil.parser.Parser
import semper.sil.ast.utility.Consistency

/**
 * A name generator for SIL.
 *
 * @author Stefan Heule
 */
class SilNameGenerator extends NameGenerator {

  def separator = "_"
  def firstCharacter = Parser.identFirstLetter.r
  def otherCharacter = Parser.identOtherLetter.r

  override def createIdentifier(input: String) = {
    super.createIdentifier(input)
  } ensuring {
    Consistency.validIdentifier(_)
  }

}
