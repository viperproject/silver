package semper.sil.ast.source

import semper.sil.ast.domains.{TypeVariableSubstitution, LogicalVariableSubstitution}
import semper.sil.ast.expressions.ProgramVariableSubstitution

/** A trait describing the location of an AST node. */
sealed trait SourceLocation

/** Describes a location in a file by line and column number. */
case class RealSourceLocation(line: Int, column: Int) extends SourceLocation {
  override def toString = "%d.%d".format(line, column)
}

/** Describes ''no location'' for cases where a `SourceLocation` is expected, but not available. */
object NoLocation extends SourceLocation

// TODO: what are the following three classes needed for?
class TypeSubstitutedSourceLocation(
                                     val original: SourceLocation,
                                     val substitution: TypeVariableSubstitution
                                     ) extends SourceLocation

class LogicalSubstitutedSourceLocation(
                                        original: SourceLocation,
                                        substitution: LogicalVariableSubstitution
                                        ) extends SourceLocation

class PVSubstitutedSourceLocation(
                                   original: SourceLocation,
                                   substitution: ProgramVariableSubstitution
                                   ) extends SourceLocation


