// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import viper.silver.ast.pretty.{Fixity, Infix, LeftAssociative, NonAssociative, Prefix, PrettyPrintPrimitives, RightAssociative}
import utility.{Consistency, DomainInstances, Nodes, Types, Visitor}
import viper.silver.ast.MagicWandStructure.MagicWandStructure
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.cfg.silver.{CfgGenerator, SilverCfg}
import viper.silver.verifier.ConsistencyError
import viper.silver.utility.{CacheHelper, DependencyAware}

import scala.collection.immutable
import scala.reflect.ClassTag

/** A Silver program. */
case class Program(domains: Seq[Domain], fields: Seq[Field], functions: Seq[Function], predicates: Seq[Predicate], methods: Seq[Method], extensions: Seq[ExtensionMember])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
  extends Node with DependencyAware with Positioned with Infoed with Scope with TransformableErrors {

  lazy val domainsByName: Map[String, Domain] = domains.map(x => (x.name, x)).toMap
  lazy val domainFunctionsByName: Map[String, DomainFunc] = domains.flatMap(_.functions).map(x => (x.name, x)).toMap
  lazy val fieldsByName: Map[String, Field] = fields.map(x => (x.name, x)).toMap
  lazy val functionsByName: Map[String, Function] = functions.map(x => (x.name, x)).toMap
  lazy val predicatesByName: Map[String, Predicate] = predicates.map(x => (x.name, x)).toMap
  lazy val methodsByName: Map[String, Method] = methods.map(x => (x.name, x)).toMap

  val scopedDecls: Seq[Declaration] =
    domains ++ fields ++ functions ++ predicates ++ methods ++ extensions ++
    domains.flatMap(d => {(d.axioms.filter(_.isInstanceOf[NamedDomainAxiom])).asInstanceOf[Seq[NamedDomainAxiom]] ++ d.functions})

  lazy val magicWandStructures: Seq[MagicWandStructure] =
    this.deepCollect({
      case wand: MagicWand => wand.structure(this)
    }).distinct

  override lazy val check : Seq[ConsistencyError] =
    Consistency.checkContextDependentConsistency(this, this) ++
    Consistency.checkNoFunctionRecursesViaPreconditions(this) ++
    checkMethodCallsAreValid ++
    checkFunctionApplicationsAreValid ++
    checkDomainFunctionApplicationsAreValid ++
    checkPredicateAccessesAreValid ++
    checkAbstractPredicatesUsage ++
    checkIdentifiers

  /** checks that formalReturns of method calls are assignable to targets, and arguments are assignable to formalArgs */
  lazy val checkMethodCallsAreValid: Seq[ConsistencyError] = methods.flatMap(m=> {
    var s = Seq.empty[ConsistencyError]

    m.body match {
      case None => /* Nothing to do */
      case Some(actualBody) =>
        for (c@MethodCall(name, args, targets) <- actualBody) {
          findMethodOptionally(name) match {
            case Some(existingMethod) =>
              if(!Consistency.areAssignable(existingMethod.formalReturns, targets))
                s :+= ConsistencyError(s"Formal returns ${existingMethod.formalReturns} of method $name are not assignable to targets $targets.", c.pos)
              if(!Consistency.areAssignable(args, existingMethod.formalArgs))
                s :+= ConsistencyError(s"Arguments $args are not assignable to formal arguments ${existingMethod.formalArgs} of method " + name, c.pos)
            case None =>
          }
        }
    }

    s
  })

  lazy val checkAbstractPredicatesUsage: Seq[ConsistencyError] =
    (predicates ++ functions ++ methods) flatMap checkAbstractPredicatesUsageIn

  private def checkAbstractPredicatesUsageIn(node: Node): Seq[ConsistencyError] = {
    var errors = Seq.empty[ConsistencyError]

    def check(loc: PredicateAccess, pos: Position): Unit = {
      findPredicateOptionally(loc.predicateName)
        .foreach(predicate => {
          if (predicate.body.isEmpty)
            errors :+= ConsistencyError(s"Cannot unfold $loc because ${loc.predicateName}  is abstract.", pos)
        })
    }

    node.visit {
      case fold: Fold => check(fold.acc.loc, fold.pos)
      case unfold: Unfold => check(unfold.acc.loc, unfold.pos)
      case unfolding: Unfolding => check(unfolding.acc.loc, unfolding.pos)
    }

    errors
  }

  /** Checks that the applied functions exists, that the arguments of function applications are assignable to
    * formalArgs, and that the type of function applications matches with the type of the function definition.
    **/
  lazy val checkFunctionApplicationsAreValid: Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]

    for (funcApp@FuncApp(name, args) <- this) {
      findFunctionOptionally(name) match {
        case None => // Consistency error already reported by checkIdentifiers
        case Some(funcDef) => {
          if (!Consistency.areAssignable(args, funcDef.formalArgs)) {
            s :+= ConsistencyError(
              s"Function $name with formal arguments ${funcDef.formalArgs} cannot be applied to provided arguments $args.",
              funcApp.pos
            )
          }
          if (funcApp.typ != funcDef.typ) {
            s :+= ConsistencyError(
              s"No matching function $name found of return type ${funcApp.typ}, instead found with return type ${funcDef.typ}.",
              funcApp.pos
            )
          }
        }
      }
    }

    s
  }

  /** Checks that the predicate access arguments are assignable to formalArgs.
    **/
  lazy val checkPredicateAccessesAreValid: Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]

    for (predAcc@PredicateAccess(args, name) <- this) {
      findPredicateOptionally(name) match {
        case None => // Consistency error already reported by checkIdentifiers
        case Some(predDef) => {
          if (!Consistency.areAssignable(args, predDef.formalArgs)) {
            s :+= ConsistencyError(
              s"Predicate $name with formal arguments ${predDef.formalArgs} cannot be used with provided arguments $args.",
              predAcc.pos
            )
          }
        }
      }
    }

    s
  }

  /** Checks that the applied domain functions exists, that the arguments of function applications are assignable to
    * formalArgs, that the type of function applications matches with the type of the function definition and that also
    * the name of the domain matches.
    */
  lazy val checkDomainFunctionApplicationsAreValid: Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]

    for (funcApp@DomainFuncApp(name, args, typVarMap) <- this) {
      findDomainFunctionOptionally(name) match {
        case None => s :+= ConsistencyError(s"No domain function named $name found in the program.", funcApp.pos)
        case Some(funcDef) => {
          if (!Consistency.areAssignable(args, funcDef.formalArgs map {
            fa =>
              // substitute parameter types
              UnnamedLocalVarDecl(fa.typ.substitute(typVarMap))(fa.pos)
          })) {
            s :+= ConsistencyError(
              s"Domain function $name with formal arguments ${funcDef.formalArgs} cannot be applied to provided arguments $args.",
              funcApp.pos
            )
          }
          if (funcApp.typ != funcDef.typ.substitute(typVarMap)) {
            s :+= ConsistencyError(
              s"No matching domain function $name found of return type ${funcApp.typ}, instead found with return type ${funcDef.typ}.",
              funcApp.pos
            )
          }
          if (funcApp.domainName != funcDef.domainName) {
            s :+= ConsistencyError(
              s"No matching domain function $name found in domain ${funcApp.domainName}, instead found in domain ${funcDef.domainName}.",
              funcApp.pos
            )
          }
        }
      }
    }

    s
  }

  /** checks that all identifier declarations and uses are valid in scope**/
  lazy val checkIdentifiers: Seq[ConsistencyError] = {

    def checkLocalVarUse(name: String, n: Positioned with Typed, declarationMap: immutable.HashMap[String, Declaration]) : Option[ConsistencyError] = {
      declarationMap.get(name) match {
        case Some(d: LocalVarDecl) => if(d.typ == n.typ) None else Some(ConsistencyError(s"No matching local variable $name found with type ${n.typ}, instead found ${d.typ}.", n.pos))
        case Some(d) => Some(ConsistencyError(s"No matching local variable $name found with type ${n.typ}, instead found other identifier of type ${d.getClass.getSimpleName}.", n.pos))
        case None => Some(ConsistencyError(s"Local variable $name not found.", n.pos))
      }
    }
    def checkNameUse[T](name: String, n: Positioned, expected: String, declarationMap: immutable.HashMap[String, Declaration])(implicit tag: ClassTag[T]) : Option[ConsistencyError] = {
      declarationMap.get(name) match {
        case Some(d) => d match {
          case _: T => None
          case _ => Some(ConsistencyError(s"No matching identifier $name found of type $expected, instead found of type ${d.getClass.getSimpleName}.", n.pos))
        }
        case None => Some(ConsistencyError(s"No matching identifier $name found of type $expected.", n.pos))
      }
    }
    def checkNameUseLabel(name: String, n: Positioned, expected: String, declarationMap: immutable.HashMap[String, Declaration]) : Option[ConsistencyError] = {
      if (name == LabelledOld.LhsOldLabel) None
      else declarationMap.get(name) match {
        case Some(d) => d match {
          case _: Label => None
          case _ => Some(ConsistencyError(s"No matching identifier $name found of type $expected, instead found of type ${d.getClass.getSimpleName}.", n.pos))
        }
        case None => Some(ConsistencyError(s"No matching identifier $name found of type $expected.", n.pos))
      }
    }

    def checkNamesInScope(currentScope: Scope, dMap: immutable.HashMap[String, Declaration]) : Seq[ConsistencyError] = {
      var newMap = immutable.HashMap.empty[String, Declaration]
      var s: Seq[ConsistencyError] = Seq.empty[ConsistencyError]
      //check name declarations
      currentScope.scopedDecls.foreach(l=> {
        if(!Consistency.validUserDefinedIdentifier(l.name))
          s :+= ConsistencyError(s"${l.name} is not a valid identifier.", l.pos)

        newMap.get(l.name) match {
          case Some(_: Declaration) => s :+= ConsistencyError(s"Duplicate identifier `${l.name}` found.", l.pos)
          case None => newMap += (l.name -> l)
        }
      })
      // Override duplicate keys in old map
      val declarationMap = dMap ++ newMap

      //check name uses
      Visitor.visitOpt(currentScope.asInstanceOf[Node], Nodes.subnodes){ n => {
        n match {
          case sc: Scope => {
            if (sc == currentScope)
              true
            else {
              n match {
                case _: DomainFunc => s ++= checkNamesInScope(sc, immutable.HashMap.empty[String, Declaration])
                case _ => s ++= checkNamesInScope(sc, declarationMap)
              }
              false
            }
          }
          case _ =>
            val optionalError = n match {
              case l: LocalVar => checkLocalVarUse(l.name, l, declarationMap)
              case m: MethodCall => checkNameUse[Method](m.methodName, m, "Method", declarationMap)
              case f: FuncApp => checkNameUse[Function](f.funcname, f, "Function", declarationMap)
              case f: DomainFuncApp => checkNameUse[DomainFunc](f.funcname, f, "DomainFunc", declarationMap)
              case f: FieldAccess => checkNameUse[Field](f.field.name, f, "Field", declarationMap)
              case p: PredicateAccess => checkNameUse[Predicate](p.predicateName, p, "Predicate", declarationMap)
              case g: Goto => checkNameUse[Label](g.target, g, "Label", declarationMap)
              case l: LabelledOld => checkNameUseLabel(l.oldLabel, l, "Label", declarationMap)
              case _ => None
            }
            optionalError match {
              case Some(error) => s :+= error
              case None =>
            }
            true
        }
      }}
      s
    }

    checkNamesInScope(this, immutable.HashMap.empty[String, Declaration])
  }

  lazy val groundTypeInstances = DomainInstances.findNecessaryTypeInstances(this)

  val members: Seq[Member with Serializable] = domains ++ fields ++ functions ++ predicates ++ methods ++ extensions

  def findFieldOptionally(name: String): Option[Field] = this.fieldsByName.get(name)

  def findField(name: String): Field = {
    findFieldOptionally(name) match {
      case Some(f) => f
      case None => sys.error("Field name " + name + " not found in program.")
    }
  }

  def findMethodOptionally(name: String): Option[Method] = this.methodsByName.get(name)

  def findMethod(name: String): Method = {
    findMethodOptionally(name) match {
      case Some(m) => m
      case None => sys.error("Method name " + name + " not found in program.")
    }
  }

  def findFunctionOptionally(name: String): Option[Function] = this.functionsByName.get(name)

  def findFunction(name: String): Function = {
    findFunctionOptionally(name) match {
      case Some(f) => f
      case None => sys.error("Function name " + name + " not found in program.")
    }
  }

  def findPredicateOptionally(name: String): Option[Predicate] = this.predicatesByName.get(name)

  def findPredicate(name: String): Predicate = {
    findPredicateOptionally(name) match {
      case Some(p) => p
      case None => sys.error("Predicate name " + name + " not found in program.")
    }
  }

  def findDomainOptionally(name: String): Option[Domain] = this.domainsByName.get(name)

  def findDomain(name: String): Domain = {
    findDomainOptionally(name) match {
      case Some(d) => d
      case None => sys.error("Domain name " + name + " not found in program.")
    }
  }

  def findDomainFunctionOptionally(name: String): Option[DomainFunc] = this.domainFunctionsByName.get(name)

  def findDomainFunction(name: String): DomainFunc = {
    findDomainFunctionOptionally(name) match {
      case Some(f) => f
      case None => sys.error("Domain function " + name + " not found in program.")
    }
  }

  override lazy val dependencyHashMap: Map[Method, String] = Map(methods.map { m =>
      val dependencies: String = m.entityHash + " " + getDependencies(this, m).map(_.entityHash).mkString(" ")
      m -> CacheHelper.buildHash(dependencies)
    }: _*)

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }

}//class Program

object Program{
  val defaultType = Int
}

trait Hashable extends Node {
  lazy val entityHash: String = CacheHelper.computeEntityHash("", this)
}

// --- Program members

/** A field declaration. */
case class Field(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Location with Typed {
  override lazy val check : Seq[ConsistencyError] =
    if(!typ.isConcrete) Seq(ConsistencyError(s"Type of field $name must be concrete, but found $typ.", pos)) else Seq()

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  val scopedDecls = Seq() //field is a scope because it is a member; it has no locals
}

/** A predicate declaration. */
case class Predicate(name: String, formalArgs: Seq[LocalVarDecl], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Location {
  override lazy val check : Seq[ConsistencyError] =
    (if (body.isDefined) Consistency.checkNonPostContract(body.get) ++ Consistency.checkWildcardUsage(body.get, false) else Seq()) ++
    (if (body.isDefined && !Consistency.noOld(body.get))
      Seq(ConsistencyError("Predicates must not contain old expressions.",body.get.pos))
     else Seq()) ++
    (if (body.isDefined && !(Consistency.noPerm(body.get) && Consistency.noForPerm(body.get)))
      Seq(ConsistencyError("perm and forperm expressions are not allowed in predicate bodies", body.get.pos)) else Seq()) ++
    {
      var errors = Seq.empty[ConsistencyError]
      if (body.isDefined) {
        StrategyBuilder.SlimVisitor[Node]({
          case m: MagicWand => errors ++= Seq(ConsistencyError("Magic wands are not supported in predicates.", m.pos))
          case _ =>
        }).execute[Node](body.get)
      }
      errors
    }

  val scopedDecls: Seq[Declaration] = formalArgs
  def isAbstract = body.isEmpty

  override def isValid : Boolean = body match {
    case Some(e) if e.contains[PermExp] => false
    case Some(e) if e.contains[ForPerm] => false
    case _ => true
  }

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}

/** A method declaration. */
case class Method(name: String, formalArgs: Seq[LocalVarDecl], formalReturns: Seq[LocalVarDecl], pres: Seq[Exp], posts: Seq[Exp], body: Option[Seqn])
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)
    extends Member with Callable with Contracted {

  /* TODO: Should not have to be a lazy val, see also the comment for method
   *       translateMemberSignature in file parser/Translator.scala
   */
  lazy val bodyOrAssumeFalse: Seqn = body match {
    case Some(actualBody) =>
      actualBody
    case None =>
      Seqn(
        Vector(Inhale(FalseLit()())()),
        Vector.empty
      )()
  }

  def deepCollectInBody[A](f: PartialFunction[Node, A]): Seq[A] = body match {
    case null => Nil
    case None => Nil
    case Some(actualBody) => actualBody.deepCollect(f)
  }

  def labels: Seq[Label] = deepCollectInBody { case l: Label => l }
  val scopedDecls: Seq[Declaration] = formalArgs ++ formalReturns ++ labels

  override lazy val check: Seq[ConsistencyError] =
    pres.flatMap(Consistency.checkPre) ++
    posts.flatMap(Consistency.checkPost) ++
    posts.flatMap(p=>{ if(!Consistency.noResult(p)) Seq(ConsistencyError("Method postconditions must have no result variables.", p.pos)) else Seq()}) ++
    body.fold(Seq.empty[ConsistencyError])(Consistency.checkNoArgsReassigned(formalArgs, _)) ++
    (if (!((formalArgs ++ formalReturns) forall (_.typ.isConcrete))) Seq(ConsistencyError("Formal args and returns must have concrete types.", pos)) else Seq()) ++
    (pres ++ posts).flatMap(Consistency.checkNoPermForpermExceptInhaleExhale) ++
    checkReturnsNotUsedInPreconditions ++
    (pres ++ posts ++ body.toSeq).flatMap(Consistency.checkWildcardUsage(_, false))

  lazy val checkReturnsNotUsedInPreconditions: Seq[ConsistencyError] = {
    val varsInPreconditions: Seq[LocalVar] = pres flatMap {_.deepCollect {case l: LocalVar => l}}
    var s = Seq.empty[ConsistencyError]
    formalReturns.foreach {f => {
      varsInPreconditions.filter(v=>{v.name == f.name && v.typ == f.typ}).foreach {v=> {
        s :+= ConsistencyError(s"Return variable ${v.name} cannot be accessed in precondition.", v.pos)
      }}
    }}
    s
  }

  override def getMetadata: Seq[Any] = {
    Seq(pos, info, errT)
  }
  /**
    * Returns a control flow graph that corresponds to this method.
    */
  def toCfg(simplify: Boolean = true, detect: Boolean = true): SilverCfg = CfgGenerator.methodToCfg(this, simplify, detect)
}

/** A function declaration */
case class Function(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, pres: Seq[Exp], posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Member with FuncLike with Contracted {
  override lazy val check : Seq[ConsistencyError] =
    posts.flatMap(p=>{ if(!Consistency.noOld(p))
      Seq(ConsistencyError("Function post-conditions must not have old expressions.", p.pos)) else Seq()}) ++
    (pres ++ posts).flatMap(Consistency.checkNoPermForpermExceptInhaleExhale) ++
    (pres ++ posts ++ body.toSeq).flatMap(Consistency.checkWildcardUsage(_, true)) ++
    (if(!(body forall (_ isSubtype typ))) Seq(ConsistencyError("Type of function body must match function type.", pos)) else Seq() ) ++
    (posts flatMap (p => if (!Consistency.noPerm(p) || !Consistency.noForPerm(p)) Seq(ConsistencyError("perm and forperm expressions are not allowed in function postconditions", p.pos)) else Seq() )) ++
    pres.flatMap(Consistency.checkPre) ++
    posts.flatMap(Consistency.checkPost) ++
    posts.flatMap(p => if (!Consistency.noPermissions(p))
      Seq(ConsistencyError("Function post-conditions must not contain permissions.", p.pos)) else Seq()) ++
    (if(body.isDefined) Consistency.checkFunctionBody(body.get) else Seq()) ++
    (if(!Consistency.noDuplicates(formalArgs)) Seq(ConsistencyError("There must be no duplicates in formal args.", pos)) else Seq()) ++
    {
      var errors = Seq.empty[ConsistencyError]
      pres.foreach(pre => {
        StrategyBuilder.SlimVisitor[Node]({
          case m: MagicWand => errors ++= Seq(ConsistencyError("Magic wands are not supported in function's preconditions.", m.pos))
          case _ =>
        }).execute[Node](pre)
      })
      errors
    }

  val scopedDecls: Seq[Declaration] = formalArgs
  /**
   * The result variable of this function (without position or info).
   */
  def result = Result(typ)()

  /**
   * Is this function recursive?
   */
  lazy val isRecursive: Boolean = body exists (_ existsDefined {
    case FuncApp(funcname, _) if name == funcname =>
  })

  def isAbstract = body.isEmpty

  lazy val isPure = pres.forall(_.isPure)

  override def isValid : Boolean /* Option[Message] */ = this match {
    case _ if (for (e <- pres ++ posts) yield e.contains[MagicWand]).contains(true) => false
    case _ if (for (e <- body)           yield e.contains[MagicWand]).contains(true) => false
    case _ if (for (e <- pres ++ posts) yield e.contains[CurrentPerm]).contains(true) => false
    case _ if (for (e <- body)           yield e.contains[CurrentPerm]).contains(true) => false
    case _ if (for (e <- pres ++ posts) yield e.contains[ForPerm]).contains(true) => false
    case _ if (for (e <- body)           yield e.contains[ForPerm]).contains(true) => false
    case _ => true
  }

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}


trait AnyLocalVarDecl extends Hashable with Positioned with Infoed with Typed with TransformableErrors {
  override def getMetadata: Seq[Any] = {
    Seq(pos, info, errT)
  }
}

// --- Unnamed local variable declarations

case class UnnamedLocalVarDecl(typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnyLocalVarDecl


// --- Local variable declarations

/**
 * Local variable declaration.  Note that these are not statements in the AST, but
 * rather occur as part of a method, loop, function, etc.
 */
case class LocalVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends AnyLocalVarDecl with Declaration {
  /**
   * Returns a local variable with equivalent information
   */
  lazy val localVar = LocalVar(name, typ)(pos, info, errT)
}


// --- Domains and domain members

/** A user-defined domain. */
case class Domain(name: String, functions: Seq[DomainFunc], axioms: Seq[DomainAxiom], typVars: Seq[TypeVar] = Nil, interpretations: Option[Map[String, String]] = None)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Member with Positioned with Infoed with TransformableErrors {

  override lazy val check : Seq[ConsistencyError] =
    if (typVars.nonEmpty && interpretations.nonEmpty) Seq(ConsistencyError("Interpreted domains cannot have type arguments.", pos)) else Seq()

  val scopedDecls = Seq()
  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  def instantiate(instantiateAs: DomainType, program: Program): Domain = {
    assert(   instantiateAs.domainName == name
           && instantiateAs.typeParameters == typVars)

    val (instantiatedFunctions, instantiatedAxioms) =
      utility.DomainInstances.getInstanceMembers(program, instantiateAs)

    Domain(name, instantiatedFunctions, instantiatedAxioms, Nil)(pos, info)
  }

  def instantiate(subst: Map[TypeVar, Type], program: Program): Domain = {
    instantiate(DomainType(this, subst), program)
  }
}

/** A domain axiom. */
sealed trait DomainAxiom extends DomainMember {
  def exp: Exp
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noResult(exp)) Seq(ConsistencyError("Axioms can never contain result variables.", exp.pos)) else Seq()) ++
    (if(!Consistency.noOld(exp)) Seq(ConsistencyError("Axioms can never contain old expressions.", exp.pos)) else Seq()) ++
    (if(!Consistency.noLocationAccesses(exp)) Seq(ConsistencyError("Axioms can never contain location accesses.", exp.pos)) else Seq()) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError("Axioms must be of Bool type", exp.pos)) else Seq()) ++
    Consistency.checkPure(exp)

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  val scopedDecls = Seq()
}

case class NamedDomainAxiom(name: String, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo,val domainName : String, val errT: ErrorTrafo = NoTrafos)
  extends DomainAxiom with Declaration

case class AnonymousDomainAxiom(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val domainName : String, val errT: ErrorTrafo = NoTrafos)
  extends DomainAxiom

object Substitution{
  type Substitution = Map[TypeVar,Type]
  def toString(s : Substitution) : String = s.mkString(",")
}
/** Domain function which is not a binary or unary operator. */
case class DomainFunc(name: String, formalArgs: Seq[AnyLocalVarDecl], typ: Type, unique: Boolean = false, interpretation: Option[String] = None)
                     (val pos: Position = NoPosition, val info: Info = NoInfo, val domainName: String, val errT: ErrorTrafo = NoTrafos)
                      extends AbstractDomainFunc with DomainMember with Declaration {
  override lazy val check : Seq[ConsistencyError] =
    if (unique && formalArgs.nonEmpty) Seq(ConsistencyError("Only constants, i.e. nullary domain functions can be unique.", pos)) else Seq()

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  val scopedDecls: Seq[Declaration] = formalArgs.filter(p => p.isInstanceOf[LocalVarDecl]).asInstanceOf[Seq[LocalVarDecl]]
}

// --- Common functionality

/** Common ancestor for members of a program. */
sealed trait Member extends Hashable with Positioned with Infoed with Scope with Declaration with TransformableErrors {
  def name: String
}

/** Common ancestor for domain members. */
sealed trait DomainMember extends Hashable with Positioned with Infoed with Scope with TransformableErrors {
  def domainName : String //TODO:make names qualified

  /** See [[viper.silver.ast.utility.Types.freeTypeVariables]]. */
  lazy val freeTypeVariables = Types.freeTypeVariables(this)
}

/** Common ancestor for things with formal arguments. */
sealed trait Callable {
  def formalArgs: Seq[AnyLocalVarDecl]
  def name: String
}

/** Common ancestor for functions and domain functions */
sealed trait FuncLike extends Callable with Typed

/** A member with a contract. */
sealed trait Contracted extends Member {
  def pres: Seq[Exp]
  def posts: Seq[Exp]
}

/** A common trait for resources (fields, predicates and magic wands) */
trait Resource extends Node with Positioned with Infoed with TransformableErrors

/** A common trait for locations (fields and predicates). */
sealed trait Location extends Member with Resource

/** Common superclass for domain functions and binary/unary operators. */
sealed trait AbstractDomainFunc extends FuncLike with Positioned with Infoed with TransformableErrors


// --- Built-in domain functions and operators

/** Built-in domain functions  */
sealed trait BuiltinDomainFunc extends AbstractDomainFunc {
  lazy val info = NoInfo
  lazy val pos = NoPosition
  lazy val errT = NoTrafos
}

/** Domain functions which are written as infix or prefix operators. */
sealed trait Op extends AbstractDomainFunc with BuiltinDomainFunc {
  lazy val name = op
  def op: String
  def fixity: Fixity
  def priority: Int
}

/** Domain functions with return type integer. */
sealed trait IntDomainFunc extends AbstractDomainFunc {
  lazy val typ = Int
}
/** Domain functions with return type boolean. */
sealed trait BoolDomainFunc extends AbstractDomainFunc {
  lazy val typ = Bool
}
/** Domain functions with return type permission. */
sealed trait PermDomainFunc extends AbstractDomainFunc {
  lazy val typ = Perm
}

/** Domain functions that represent built-in binary operators */
sealed trait BinOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("left", leftTyp)(), LocalVarDecl("right", rightTyp)())
  def leftTyp: Type
  def rightTyp: Type
}

/** Left associative operator. */
sealed trait LeftAssoc {
  lazy val fixity = Infix(LeftAssociative)
}

/** Domain functions that represent built-in binary operators where both arguments are integers. */
sealed trait IntBinOp extends BinOp {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Domain functions that represent built-in binary operators where both arguments are booleans. */
sealed trait BoolBinOp extends BinOp {
  lazy val leftTyp = Bool
  lazy val rightTyp = Bool
}

/** Domain functions that represent built-in binary operators where both arguments are permissions. */
sealed trait PermBinOp extends BinOp {
  lazy val leftTyp = Perm
  lazy val rightTyp = Perm
}

/** Domain functions that represent built-in unary operators */
sealed trait UnOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("exp", expTyp)())
  def expTyp: Type
}

/** Common interface for sum operators. */
sealed abstract class SumOp(val op: String) extends LeftAssoc {
  lazy val priority = 8
}
/** Common interface for product operators. */
sealed abstract class ProdOp(val op: String) extends LeftAssoc {
  lazy val priority = 9
}
/** Common interface for relational operators. */
sealed abstract class RelOp(val op: String) extends BoolDomainFunc {
  lazy val priority = 7
  lazy val fixity = Infix(NonAssociative)
}

// Arithmetic integer operators
case object AddOp extends SumOp("+") with IntBinOp with IntDomainFunc
case object SubOp extends SumOp("-") with IntBinOp with IntDomainFunc
case object MulOp extends ProdOp("*") with IntBinOp with IntDomainFunc
case object DivOp extends ProdOp("\\") with IntBinOp with IntDomainFunc
case object ModOp extends ProdOp("%") with IntBinOp with IntDomainFunc

// Arithmetic permission operators
case object PermAddOp extends SumOp("+") with PermBinOp with PermDomainFunc
case object PermSubOp extends SumOp("-") with PermBinOp with PermDomainFunc
case object PermMulOp extends ProdOp("*") with PermBinOp with PermDomainFunc
case object DebugPermMinOp extends SumOp("min") with PermBinOp with PermDomainFunc
case object IntPermMulOp extends ProdOp("*") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Perm
}
case object PermDivOp extends ProdOp("/") with BinOp with PermDomainFunc {
  lazy val leftTyp = Perm
  lazy val rightTyp = Int
}
case object FracOp extends ProdOp("/") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Integer negation. */
case object NegOp extends UnOp with IntDomainFunc {
  lazy val expTyp = Int
  lazy val op = "-"
  lazy val priority = 10
  lazy val fixity = Prefix
}

case object PermNegOp extends UnOp with PermDomainFunc {
  lazy val expTyp = Perm
  lazy val op = "-"
  lazy val priority = 10
  lazy val fixity = Prefix
}

// Integer comparison operators
case object LtOp extends RelOp("<") with IntBinOp
case object LeOp extends RelOp("<=") with IntBinOp
case object GtOp extends RelOp(">") with IntBinOp
case object GeOp extends RelOp(">=") with IntBinOp

// Permission comparison operators
case object PermLtOp extends RelOp("<") with PermBinOp
case object PermLeOp extends RelOp("<=") with PermBinOp
case object PermGtOp extends RelOp(">") with PermBinOp
case object PermGeOp extends RelOp(">=") with PermBinOp

/** Boolean or. */
case object OrOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "||"
  lazy val priority = 4
}

/** Boolean and. */
case object AndOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "&&"
  lazy val priority = 5
}

/** Boolean implication. */
case object ImpliesOp extends BoolBinOp with BoolDomainFunc {
  lazy val op = "==>"
  lazy val priority = 2
  lazy val fixity = Infix(RightAssociative)
}

/** Separating implication/Magic Wand. */
case object MagicWandOp extends BoolBinOp with AbstractDomainFunc with Resource {
  lazy val typ = Wand
  lazy val op = "--*"
  lazy val priority = 3
  lazy val fixity = Infix(RightAssociative)
}

/** Boolean negation. */
case object NotOp extends UnOp with BoolDomainFunc {
  lazy val expTyp = Bool
  lazy val op = "!"
  lazy val priority = 10
  lazy val fixity = Prefix
}

object BackendFunc {
  def apply(name: String, smtName: String, domain: String, typ: Type, formalArgs: Seq[LocalVarDecl])
                    (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): DomainFunc = {
    DomainFunc(name, formalArgs, typ, false, Some(smtName))(pos, info, domain, errT)
  }

  def unapply(df: DomainFunc) =
    if (df.interpretation.isDefined) Some((df.name, df.interpretation.get, df.typ, df.formalArgs)) else None
}

/**
  * The Extension Member trait provides the way to expand the Ast to include new Top Level declarations
  */
trait ExtensionMember extends Member with Serializable {
  def extensionSubnodes: Seq[Node]
  def prettyPrint: PrettyPrintPrimitives#Cont
}
