package semper.sil.parser

import collection.immutable.Stack
import collection.immutable

/**
 * General implementation of environments as stacked scopes.  The objects
 * associated with names in environments are of type Entity.
 *
 * Note: this class has is based on code from the kiama example called oberon0.
 */
trait Environment {

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
  sealed trait NamedEntity extends Entity with Named

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

  /**
   * Reset the environment module.
   */
  def resetEnvironments() {
    Named.resetCount()
  }

  /**
   * Static support for entity names.
   */
  object Named {

    /**
     * Count of the named things that have been produced so far.
     */
    var count = 0

    /**
     * Reset the entity count.
     */
    def resetCount() {
      count = 0
    }

  }

  /**
   * Support for unique ids for named things.
   */
  trait Named {

    import Named.count

    /**
     * The underlying name of this thing.
     */
    def name: String

    /**
     * A unique number to represent this thing.
     */
    private val num = {
      count = count + 1
      count
    }

    /**
     * A unique identifier for this thing, incorporating the underlying
     * name and its unique number.
     */
    val id = name + num

    /**
     * Still print named things as their underlying name.
     */
    override def toString: String = name

  }

  /**
   * A scope maps identifiers to entities.
   */
  type Scope = Map[String, Entity]

  /**
   * An environment is a stack of scopes with the innermost scope on the top.
   */
  type Environment = Stack[Scope]

  /**
   * Create a root environment, i.e., one that has a single scope containing
   * the given bindings.
   */
  def rootenv(bindings: (String, Entity)*): Environment =
    Stack(immutable.HashMap(bindings: _*))

  /**
   * Enter a new empty scope nested within the given environment.
   */
  def enter(env: Environment): Environment =
    env.push(new immutable.HashMap[String, Entity])

  /**
   * Leave the outermost scope of the given environment, raising an error if
   * the environment is empty.
   */
  def leave(env: Environment): Environment =
    if (env.isEmpty)
      sys.error("leave called on empty environment")
    else
      env.pop

  /**
   * Define i to be e in the current scope of env, raising an error if the
   * environment is empty.
   */
  def define(env: Environment, i: String, e: Entity): Environment = {
    if (env.isEmpty)
      sys.error("define called on empty environment")
    else {
      val s = env.top
      env.pop.push(s + ((i, e)))
    }
  }

  /**
   * Say whether i is defined in the current scope of env.
   */
  def isDefinedInScope(env: Environment, i: String): Boolean =
    env.nonEmpty && ((env.top) contains i)

  /**
   * Say whether i is defined in the given scope.
   */
  def isDefinedInScope(scope: Scope, i: String): Boolean =
    scope contains i

  /**
   * Say whether i is defined in any scope of env.
   */
  def isDefinedInEnv(env: Environment, i: String): Boolean =
    env.exists(s => isDefinedInScope(s, i))

  /**
   * Say whether i is defined in an innermost scope of env (i.e., in the
   * current scope).
   */
  def isDefinedInInner(env: Environment, i: String): Boolean =
    isDefinedInScope(env.top, i)

  /**
   * Say whether i is defined in an outer scope of env (i.e., not in the
   * current scope).
   */
  def isDefinedInOuter(env: Environment, i: String): Boolean =
    isDefinedInEnv(env.pop, i)

  /**
   * Look up i in env, returning the mapped Entity if there is one, otherwise
   * return e.  If scope is true, just search the innermost scope, otherwise
   * search outwards in all scopes, returning the first Entity found, if any.
   */
  def lookup(env: Environment, i: String, e: Entity, scope: Boolean = false): Entity =
    if (env.isEmpty)
      e
    else if (scope)
      env.top.getOrElse(i, e)
    else if (isDefinedInScope(env, i))
      env.top(i)
    else
      lookup(env.pop, i, e)

}
