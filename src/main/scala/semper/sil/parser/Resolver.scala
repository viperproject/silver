package semper.sil.parser

import org.kiama.util.Messaging.message
import org.kiama.util.Messaging.messagecount

/**
 * A resolver and type-checker for our intermediate SIL AST.  The approach is based on the example
 * called oberon0 from kiama.
 */
object Resolver {
  def analyser = Seq(NameAnalyser())

  def run(p: PProgram) {
    analyser foreach {
      a => a.run(p)
      if (messagecount > 0) return
    }
  }
}

trait Analyser {

  /**
   * Run the resolver, reporting any potential errors.
   */
  def run(p: PProgram)

}

case class NameAnalyser() extends Analyser with Environment {

  private val idnMap = collection.mutable.HashMap[String, Entity]()

  def run(p: PProgram) {
    // find all declarations
    p.visit {
      case i@PIdnDef(name) =>
        idnMap.get(name) match {
          case Some(MultipleEntity()) =>
            message(i, s"$name already defined.")
          case Some(e) =>
            message(i, s"$name already defined.")
            idnMap.put(name, MultipleEntity())
          case None =>
            val e = i.parent match {
              case decl: PProgram => ProgramEnt(decl)
              case decl: PMethod => MethodEnt(decl)
              case decl: PLocalVarDecl => LocVarEnt(decl)
              case decl: PFormalArgDecl => FormalArgEnt(decl)
              case _ => sys.error(s"unexpected parent of identifier: ${i.parent}")
            }
            idnMap.put(name, e)
        }
      case _ =>
    }
    // check all identifier uses
    p visit {
      case i@PIdnUse(name) =>
        idnMap.getOrElse(name, UnknownEntity()) match {
          case UnknownEntity() =>
            message(i, s"$name has not been defined.")
          case _ =>
        }
      case _ =>
    }
  }
}
