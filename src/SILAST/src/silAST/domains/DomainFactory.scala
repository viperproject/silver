package silAST.domains

import silAST.programs.ProgramFactory

class DomainFactory private[domains](
    val programFactory : ProgramFactory,
    val name : String
  )
{

}