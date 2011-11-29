package silAST.domains

import silAST.programs.ProgramFactory

class DomainFactory private[silAST](
    val programFactory : ProgramFactory,
    val name : String
  )
{

}