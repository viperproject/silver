/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

import viper.silver.ast.pretty._
import utility.{Consistency, DomainInstances, Types}
import viper.silver.cfg.silver.CfgGenerator
import viper.silver.verifier.ConsistencyError
import viper.silver.utility.{DependencyAware, CacheHelper}

/** A Silver program. */
case class Program(domains: Seq[Domain], fields: Seq[Field], functions: Seq[Function], predicates: Seq[Predicate], methods: Seq[Method])
                  (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Node with Positioned with Infoed with TransformableErrors {


  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.noDuplicates(
    (members map (_.name)) ++
    (domains flatMap (d => (d.axioms map (_.name)) ++ (d.functions map (_.name))))))
    Seq(ConsistencyError("Names of members must be distinct.", pos)) else Seq()) ++
    Consistency.checkContextDependentConsistency(this) ++
    Consistency.checkNoFunctionRecursesViaPreconditions(this) ++
    checkMethodCallsAreValid ++
    checkFuncAppsAreValid ++
    checkDomainFuncAppsAreValid

  /** checks that each MethodCall calls an existing method and if so, checks that formalReturns are assignable to targets */
  lazy val checkMethodCallsAreValid: Seq[ConsistencyError] = methods.flatMap(m=> {
    var s = Seq.empty[ConsistencyError]
    for (c@MethodCall(name, args, targets) <- m.body) {
      methods.find(_.name == name) match{
        case Some(existingMethod) =>
          if(!Consistency.areAssignable(existingMethod.formalReturns, targets))
            s :+= ConsistencyError(s"Formal returns ${existingMethod.formalReturns} of method $name are not assignable to targets $targets.", c.pos)
          if(!Consistency.areAssignable(args, existingMethod.formalArgs))
            s :+= ConsistencyError(s"Arguments $args are not assignable to formal arguments ${existingMethod.formalArgs} of method " + name, c.pos)
        case None =>
          s :+= ConsistencyError(s"Method name $name not found in program.", c.pos)
      }
    }
    s
  })

  /** checks that each FuncApp calls an existing function */
  lazy val checkFuncAppsAreValid: Seq[ConsistencyError] = {
    val nodes: Seq[Node] = functions ++ predicates ++ methods
    val funcApps: Seq[FuncApp] =
      nodes.flatMap(_.deepCollect({case fa: FuncApp => fa}))

    funcApps.flatMap (fa => {
      functions.find(_.name == fa.funcname) match{
        case Some(existingFunction) => Seq()
        case None => Seq(ConsistencyError(s"Function name ${fa.funcname} not found in program.", fa.pos))
      }
    })
  }

  /** checks that each DomainFuncApp calls an existing domain function */
  lazy val checkDomainFuncAppsAreValid: Seq[ConsistencyError] = {
    val nodes: Seq[Node] = domains ++ functions ++ predicates ++ methods
    val domainFuncs: Seq[DomainFunc] = domains flatMap { _.functions }
    val domainFuncApps: Seq[DomainFuncApp] =
      nodes.flatMap(_.deepCollect({case fa: DomainFuncApp => fa}))

    domainFuncApps.flatMap (fa => {
        domainFuncs.find(_.name == fa.funcname) match{
          case Some(existingDomainFunction) => Seq()
          case None => Seq(ConsistencyError(s"Domain Function name ${fa.funcname} not found in program.", fa.pos))
        }
    })
  }

  lazy val groundTypeInstances = DomainInstances.findNecessaryTypeInstances(this)

  lazy val members = domains ++ fields ++ functions ++ predicates ++ methods

  def findField(name: String): Field = {
    this.fields.find(_.name == name) match {
      case Some(f) => f
      case None => sys.error("Field name " + name + " not found in program.")
    }
  }

  def findMethod(name: String): Method = {
    this.methods.find(_.name == name) match {
      case Some(m) => m
      case None => sys.error("Method name " + name + " not found in program.")
    }
  }

  def findFunctionOptionally(name: String): Option[Function] = this.functions.find(_.name == name)

  def findFunction(name: String): Function = {
    findFunctionOptionally(name) match {
      case Some(f) => f
      case None => sys.error("Function name " + name + " not found in program.")
    }
  }

  def findPredicate(name: String): Predicate = {
    this.predicates.find(_.name == name) match {
      case Some(p) => p
      case None => sys.error("Predicate name " + name + " not found in program.")
    }
  }

  def findDomain(name: String): Domain = {
    this.domains.find(_.name == name) match {
      case Some(d) => d
      case None => sys.error("Domain name " + name + " not found in program.")
    }
  }

  def findDomainFunction(name: String): DomainFunc = {
    this.domains.flatMap(_.functions).find(_.name == name) match {
      case Some(f) => f
      case None => sys.error("Domain function " + name + " not found in program.")
    }
  }
  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }

}//class Program

object Program{
  val defaultType = Int
}

// --- Program members

/** A field declaration. */
case class Field(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Location with Typed {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Field name must be a valid identifier.", pos)) else Seq()) ++
    (if(!typ.isConcrete) Seq(ConsistencyError(s"Type of field $name must be concrete, but found $typ.", pos)) else Seq())

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}

/** A predicate declaration. */
case class Predicate(name: String, formalArgs: Seq[LocalVarDecl], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Location {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Predicate name must be a valid identifier.", pos)) else Seq()) ++
    (if (body.isDefined) Consistency.checkNonPostContract(body.get) else Seq()) ++
    (if (body.isDefined && !(Consistency.noPerm(body.get) && Consistency.noForPerm(body.get)))
      Seq(ConsistencyError("perm and forperm expressions are not allowed in predicate bodies", body.get.pos)) else Seq())

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
case class Method(name: String, formalArgs: Seq[LocalVarDecl], formalReturns: Seq[LocalVarDecl], pres: Seq[Exp], posts: Seq[Exp], locals: Seq[LocalVarDecl], body: Stmt)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Member with Callable with Contracted with DependencyAware {

  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Method name must be a valid identifier.", pos)) else Seq()) ++
    pres.flatMap(Consistency.checkPre) ++
    posts.flatMap(Consistency.checkPost) ++
    posts.flatMap(p=>{ if(!Consistency.noResult(p)) Seq(ConsistencyError("Method postconditions must have no result variables.", p.pos)) else Seq()}) ++
    Consistency.checkNoArgsReassigned(formalArgs, body) ++
    (if(!noDuplicates) Seq(ConsistencyError("There must be no duplicates in names of local variables and formal args.", pos)) else Seq()) ++
    (if (!((formalArgs ++ formalReturns) forall (_.typ.isConcrete))) Seq(ConsistencyError("Formal args and returns must have concrete types.", pos)) else Seq()) ++
    (pres ++ posts).flatMap(Consistency.checkNoPermForpermExceptInhaleExhale) ++
    checkGotoAndStateLabels

  /** checks that all goto targets and state labels are existing labels and there are no duplicate labels */
  lazy val checkGotoAndStateLabels: Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    val gotos : Seq[Goto] = body.deepCollect({case g: Goto => g})
    val labels : Seq[Label] = body.deepCollect({case l: Label => l})
    val olds : Seq[LabelledOld] = body.deepCollect({case l: LabelledOld => l})

    val labelMap = scala.collection.mutable.HashMap[String, Label]()
    labels.foreach(l=>{
      labelMap.get(l.name) match {
        case Some(existingLabel) => s:+= ConsistencyError(s"Duplicate label ${l.name} found in method.", l.pos)
        case None => labelMap.put(l.name, l)
      }
    })

    gotos.foreach(g=> {
      labels.find(_.name == g.target) match {
        case Some(existingLabel) =>
        case None => s :+= ConsistencyError(s"Label ${g.target} not found in method.", g.pos)
      }
    })
    olds.foreach(o=> {
      labels.find(_.name == o.oldLabel) match {
        case Some(existingLabel) =>
        case None => s :+= ConsistencyError(s"Label ${o.oldLabel} not found in method.", o.pos)
      }
    })
    s
  }

  private def noDuplicates = Consistency.noDuplicates(formalArgs ++ Consistency.nullValue(locals, Nil) ++ Seq(LocalVar(name)(Bool)))

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  /**
    * Returns a control flow graph that corresponds to this method.
    */
  def toCfg(simplify: Boolean = true) = CfgGenerator.methodToCfg(this, simplify)

  override lazy val dependencyHash:String = {
    val dependencies:String = this.entityHash + " " + getDependencies(this).map(m =>m.entityHash).mkString(" ")
    CacheHelper.buildHash(dependencies)
  }
}

/** A function declaration */
case class Function(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, pres: Seq[Exp], posts: Seq[Exp], body: Option[Exp])
                   (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Member with FuncLike with Contracted {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Function name must be a valid identifier.", pos)) else Seq()) ++
    posts.flatMap(p=>{ if(!Consistency.noOld(p))
      Seq(ConsistencyError("Function post-conditions must not have old expressions.", p.pos)) else Seq()}) ++
    (pres ++ posts).flatMap(p=> {
      if(!Consistency.noPerm(p) || !Consistency.noForPerm(p))
        Seq(ConsistencyError("Function contracts must not have perm or forperm expressions.", p.pos)) else Seq()}) ++
    (if(!(body map (_ isSubtype typ) getOrElse true)) Seq(ConsistencyError("Type of function body must match function type.", pos)) else Seq() ) ++
    pres.flatMap(Consistency.checkPre) ++
    posts.flatMap(Consistency.checkPost) ++
    (if(body.isDefined) Consistency.checkFunctionBody(body.get) else Seq()) ++
    (if(!Consistency.noDuplicates(formalArgs)) Seq(ConsistencyError("There must be no duplicates in formal args.", pos)) else Seq())

  /**
   * The result variable of this function (without position or info).
   */
  def result = Result()(typ)

  /**
   * Is this function recursive?
   */
  def isRecursive: Boolean = body exists (_ existsDefined {
    case FuncApp(funcname, _) if name == funcname =>
  })

  def isAbstract = body.isEmpty

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


// --- Local variable declarations

/**
 * Local variable declaration.  Note that these are not statements in the AST, but
 * rather occur as part of a method, loop, function, etc.
 */
case class LocalVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Node with Positioned with Infoed with Typed with TransformableErrors {
  override lazy val check : Seq[ConsistencyError] =
    if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Local variable name must be valid identifier.", pos)) else Seq()

  /**
   * Returns a local variable with equivalent information
   */
  lazy val localVar = LocalVar(name)(typ, pos, info, errT)

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}


// --- Domains and domain members

/** A user-defined domain. */
case class Domain(name: String, functions: Seq[DomainFunc], axioms: Seq[DomainAxiom], typVars: Seq[TypeVar] = Nil)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends Member with Positioned with Infoed with TransformableErrors {
  override lazy val check : Seq[ConsistencyError] =
    if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Domain name must be valid identifier", pos)) else Seq()

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
case class DomainAxiom(name: String, exp: Exp)
                      (val pos: Position = NoPosition, val info: Info = NoInfo,val domainName : String, val errT: ErrorTrafo = NoTrafos)
  extends DomainMember {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Axiom name must be valid identifier", pos)) else Seq()) ++
    (if(!Consistency.noResult(exp)) Seq(ConsistencyError("Axioms can never contain result variables.", exp.pos)) else Seq()) ++
    (if(!Consistency.noOld(exp)) Seq(ConsistencyError("Axioms can never contain old expressions.", exp.pos)) else Seq()) ++
    (if(!Consistency.noAccessLocation(exp)) Seq(ConsistencyError("Axioms can never contain access locations.", exp.pos)) else Seq()) ++
    (if(!(exp isSubtype Bool)) Seq(ConsistencyError("Axioms must be of Bool type", exp.pos)) else Seq()) ++
    Consistency.checkPure(exp)

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}

object Substitution{
  type Substitution = Map[TypeVar,Type]
  def toString(s : Substitution) : String = s.mkString(",")
}
/** Domain function which is not a binary or unary operator. */
case class DomainFunc(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, unique: Boolean = false)
                     (val pos: Position = NoPosition, val info: Info = NoInfo,val domainName : String, val errT: ErrorTrafo = NoTrafos)
                      extends AbstractDomainFunc with DomainMember {
  override lazy val check : Seq[ConsistencyError] =
    (if(!Consistency.validUserDefinedIdentifier(name)) Seq(ConsistencyError("Domain function name must be valid identifier", pos)) else Seq()) ++
    (if(unique && formalArgs.nonEmpty) Seq(ConsistencyError("Only constants, i.e. nullary domain functions can be unique.", pos)) else Seq()) ++
    (if(!Consistency.noDuplicates(formalArgs)) Seq(ConsistencyError("There must be no duplicates in formal args.", formalArgs.head.pos)) else Seq())

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
}

// --- Common functionality

/** Common ancestor for members of a program. */
sealed trait Member extends Node with Positioned with Infoed with TransformableErrors {
  def name: String
  lazy val entityHash: String = CacheHelper.computeEntityHash("", this)
}

/** Common ancestor for domain members. */
sealed trait DomainMember extends Node with Positioned with Infoed with TransformableErrors {
  def name: String
  def domainName : String //TODO:make names qualified

  /** See [[viper.silver.ast.utility.Types.freeTypeVariables]]. */
  lazy val freeTypeVariables = Types.freeTypeVariables(this)
}

/** Common ancestor for things with formal arguments. */
sealed trait Callable {
  def formalArgs: Seq[LocalVarDecl]
  def name: String
}

/** Common ancestor for functions and domain functions */
sealed trait FuncLike extends Callable with Typed

/** A member with a contract. */
sealed trait Contracted extends Member {
  def pres: Seq[Exp]
  def posts: Seq[Exp]
}

/** A common trait for locations (fields and predicates). */
sealed trait Location extends Member

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
case object MagicWandOp extends BoolBinOp with AbstractDomainFunc {
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
