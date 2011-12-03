package silAST.domains

import silAST.expressions.DExpressionFactory
import silAST.programs.{NodeFactory, ProgramFactory}

final class DomainFactory private[silAST](
                                     val programFactory: ProgramFactory,
                                     val name: String
                                     ) extends NodeFactory with DExpressionFactory
{

}