package semper.sil.parser

import org.kiama.util.Messaging.message
import org.kiama.util.Messaging.messagecount

/**
 * A resolver and type-checker for the intermediate SIL AST.
 */
object Resolver {
  val names = NameAnalyser()

  def run(p: PProgram) {
    if (names.run(p)) {

    }
  }
}

/**
 * Resolves identifiers to their declaration.
 */
case class NameAnalyser() extends Environments {

  private val idnMap = collection.mutable.HashMap[String, Entity]()

  def run(p: PProgram): Boolean = {
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
            message(i, s"$name not defined.")
          case _ =>
        }
      case _ =>
    }
    messagecount == 0
  }
}

/**
 * General implementation of environments as stacked scopes.
 */
trait Environments {

  /** An entity is some kind of definition */
  sealed trait Entity
  case class LocVarEnt(decl: PLocalVarDecl) extends NamedEntity {
    val name = decl.idndef.name
  }
  case class MethodEnt(decl: PMethod) extends NamedEntity {
    val name = decl.idndef.name
  }
  case class FormalArgEnt(decl: PFormalArgDecl) extends NamedEntity {
    val name = decl.idndef.name
  }
  case class ProgramEnt(decl: PProgram) extends NamedEntity {
    val name = decl.idndef.name
  }

  /**
   * A named entity.
   */
  sealed trait NamedEntity extends Entity

  /**
   * An entity that represents an error situation.  These entities are
   * usually accepted in most situations to avoid cascade errors.
   */
  abstract class ErrorEntity(name: String) extends Entity

  /**
   * A entity represented by names for whom we have seen more than one
   * declaration so we are unsure what is being represented.
   */
  case class MultipleEntity() extends ErrorEntity("multiple")

  /**
   * An unknown entity, represented by names whose declarations are missing.
   */
  case class UnknownEntity() extends ErrorEntity("unknown")

}
