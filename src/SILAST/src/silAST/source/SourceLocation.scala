package silAST.source

import silAST.domains.{TypeVariableSubstitution, LogicalVariableSubstitution}
import silAST.expressions.ProgramVariableSubstitution


abstract class SourceLocation

class TypeSubstitutedSourceLocation(
    val original : SourceLocation,
    val substitution : TypeVariableSubstitution
  ) extends SourceLocation

class LogicalSubstitutedSourceLocation(
                                     original : SourceLocation,
                                     substitution : LogicalVariableSubstitution
                                     ) extends SourceLocation

class PVSubstitutedSourceLocation(
                                        original : SourceLocation,
                                        substitution : ProgramVariableSubstitution
                                        ) extends SourceLocation


object noLocation extends SourceLocation