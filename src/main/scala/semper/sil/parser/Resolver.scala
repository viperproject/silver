package semper.sil.parser

import org.kiama.attribution.Decorators._
import org.kiama._
import attribution.Decorators.Chain
import org.kiama.attribution.Attribution.attr
import org.kiama.util.Messaging.message
import util.Patterns.HasParent

/**
 * A resolver and type-checker for our intermediate SIL AST.  The approach is based on the example
 * called oberon0 from kiama.
 */
object Resolver extends NameAnalyser

trait Analyser {

  /**
   * Check an AST node for semantic errors such as invalid types or uses of expressions in
   * places they are not allowed.  Errors are reported using kiama's messaging framework.
   * By default, all child nodes are checked.
   */
  def check(n: PNode) {
    for (child <- n.children)
      check(child.asInstanceOf[PNode])
  }
}

trait NameAnalyser extends Analyser with Environment {

  override def check(n: PNode) {
    println("check: " + n)
    n match {
      case d@PIdnDef(i) if d -> entity == MultipleEntity() =>
        message(d, i + " is already declared")

      case u@PIdnUse(i) if u -> entity == UnknownEntity() =>
        message(u, i + " is not declared")

      case _ =>
      // Do nothing by default
    }

    super.check(n)
  }

  /**
   * The entity for an identifier definition as given by its declaration
   * context.
   */
  def entityFromDecl(n: PIdnDef, i: String): Entity = {
    n.parent match {
      case p: PMethod => MethodEnt(p)
      case p: PLocalVarDecl => LocVarEnt(p)
      case p: PFormalArgDecl => FormalArgEnt(p)
    }
  }

  /**
   * The default environment.
   */
  def defenv: Environment =
    rootenv(defenvPairs: _*)

  def defenvPairs: List[(String, Entity)] =
    List()

  /**
   * The program entity referred to by an identifier definition or use.  In
   * the case of a definition it's the thing being defined, so define it to
   * be a reference to the declaration.  If it's already defined, return a
   * entity that indicates a multiple definition.  In the case of a use,
   * it's the thing defined elsewhere that is being referred to here, so
   * look it up in the environment.
   */
  lazy val entity: Identifier => Entity =
    attr("entity") {
      case n@PIdnDef(i) => println("entity: "+n)
        if (isDefinedInScope(n -> (env.in), i))
          MultipleEntity()
        else
          entityFromDecl(n, i)
      case n@PIdnUse(i) => println("entity: "+n)
        lookup(n -> (env.in), i, UnknownEntity())
    }

  /**
   * The environment containing bindings for all identifiers visible at the
   * given node.  It starts at the module declaration with the default
   * environment.  At blocks we enter a nested scope which is removed on
   * exit from the block.  At constant and type declarations the left-hand
   * side binding is not in scope on the right-hand side.  Each identifier
   * definition just adds its binding to the chain.  The envout cases for
   * assignment and expression mean that we don't need to traverse into
   * those constructs, since declarations can't occur there.
   */
  lazy val env: Chain[PNode, Environment] =
    chain(envin, envout)

  def envin(in: PNode => Environment): PNode ==> Environment = {
    case _: PMethod => enter(defenv)
    case HasParent(_: PExp, p: PLocalVarDecl) => p -> (env.in)
  }

  def envout(out: PNode => Environment): PNode ==> Environment = {
    case m: PMethod => println("envout: "+m); leave(out(m))
    case p@PLocalVarDecl(d, _, _) => println("envout: "+p); d -> env
    case p@PFormalArgDecl(d, _) => println("envout: "+p); d -> env
    case n@PIdnDef(i) => println("envout: "+n); define(n -> out, i, n -> entity)
    case a => println("envout: "+a); a -> (env.in)
  }
}
