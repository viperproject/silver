package silAST.source

import silAST.domains.{TypeSubstitution, LogicalVariableSubstitution}


abstract class SourceLocation

class TypeSubstitutedSourceLocation(
    val original : SourceLocation,
    val substitution : TypeSubstitution
  ) extends SourceLocation

class LogicalSubstitutedSourceLocation(
                                     original : SourceLocation,
                                     substitution : LogicalVariableSubstitution
                                     ) extends TypeSubstitutedSourceLocation(original,substitution)


object noLocation extends SourceLocation