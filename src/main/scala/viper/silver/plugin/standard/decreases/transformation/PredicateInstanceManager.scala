// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{SimpleContext, Strategy, Traverse}
import viper.silver.ast.{AccessPredicate, BinExp, CondExp, Domain, DomainFunc, DomainFuncApp, DomainType, Exp, FieldAccessPredicate, If, Implies, Inhale, Int, LocalVar, LocalVarAssign, LocalVarDecl, MagicWand, Node, Position, PredicateAccess, PredicateAccessPredicate, Seqn, SimpleInfo, Stmt, Type, TypeVar, UnExp, Unfold}
import viper.silver.plugin.standard.decreases.{DecreasesContainer, DecreasesTuple}
import viper.silver.plugin.standard.predicateinstance.PredicateInstance
import viper.silver.verifier.ConsistencyError

import scala.collection.immutable.ListMap

/**
  * Utility functions to create predicate instances and nested relations on them.
  *
  * The following features have to be defined in the program (program field of ProgramManager)
  * otherwise a consistency error is issued.
  * "nestedPredicates" domain function
  * "PredicateInstance" domain
  */
trait PredicateInstanceManager extends ProgramManager with ErrorReporter {

  val nestedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("nestedPredicates")
  val PredicateInstanceDomain: Option[Domain] =  program.domains.find(_.name == "PredicateInstance") // findDomainOptionally()?

  protected def containsPredicateInstances(dc: DecreasesContainer): Boolean = {
    dc match {
      case DecreasesContainer(Some(DecreasesTuple(tupleExpressions, _)), _, _) =>
        tupleExpressions.exists(t => t.isSubtype(PredicateInstance.getType))
      case _ => false
    }
  }

  val addNestedPredicateInformation: Strategy[Node, SimpleContext[Node]] = ViperStrategy.Slim({
    case unfold: Unfold =>
      generateUnfoldNested(unfold.acc)
  }, t = Traverse.BottomUp)

  /**
    * Generates an Unfold with the given predicate access predicate.
    * Additionally adds the predicate instances and the nested relations.
    * @param pap the predicate access predicate
    * @return Seqn(PredicateInstance p1, Unfold(pap), [PredicateInstance p2, Inhale(Nested(p2, p1))])
    */
  protected def generateUnfoldNested(pap: PredicateAccessPredicate): Stmt = {

    if (PredicateInstanceDomain.isDefined && nestedFunc.isDefined) {
      // assign variable to "predicate" before unfold
      val varP = uniquePredicateInstanceVar(pap.loc)
      val assignP = generatePredicateAssign(varP.localVar, pap.loc)

      val unfold = Unfold(pap)()

      val nested: Stmt = {
        val pred = program.findPredicate(pap.loc.predicateName)
        pred.body match {
          case Some(body) =>
            if (PredicateInstanceDomain.isDefined && nestedFunc.isDefined) {
              val formalArgs = ListMap(pred.formalArgs.map(_.localVar).zip(pap.loc.args): _*)
              //Generate nested-assumption
              transformPredicateBody(body.replace(formalArgs), varP, pap.perm)
            } else {
              // at least one of Loc domain or nested function is not defined
              if (PredicateInstanceDomain.isEmpty) {
                reportPredicateInstanceNotDefined(pap.pos)
              }
              if (nestedFunc.isEmpty) {
                reportNestedNotDefined(pap.pos)
              }
              EmptyStmt
            }
          case None => EmptyStmt //Predicate has no body
        }
      }
      Seqn(Seq(assignP, unfold, nested), Seq(varP))()

    } else {
      // at least one of Loc domain or nested function is not defined
      if (PredicateInstanceDomain.isEmpty) {
        reportPredicateInstanceNotDefined(pap.pos)
      }
      if (nestedFunc.isEmpty) {
        reportNestedNotDefined(pap.pos)
      }
      EmptyStmt
    }
  }

  /**
    * Traverses a predicate body (once) and adds corresponding inhales of the 'nested'-Relation
    * iff a predicate is inside of this body.
    * PredicateInstanceDomain and nestedPredication function must be defined!
    * @param body the part of the predicate-body which should be transform
    * @param unfoldedPredVar the body of the original predicate which should be analyzed
    * @return statements with the generated inhales: (Inhale(nested(pred1, pred2)))
    */
  private def transformPredicateBody(body: Exp, unfoldedPredVar: LocalVarDecl, unfoldPermission: Exp): Stmt = {
    body match {
      case ap: AccessPredicate => ap match {
        case FieldAccessPredicate(_, _) => EmptyStmt
        case calledPred: PredicateAccessPredicate =>
          assert(PredicateInstanceDomain.isDefined)
          assert(nestedFunc.isDefined)

          //local variables
          val varOfCallerPred: LocalVarDecl = unfoldedPredVar
          val varOfCalleePred: LocalVarDecl = uniquePredicateInstanceVar(calledPred.loc)

          //assignment
          val assign = generatePredicateAssign(varOfCalleePred.localVar, calledPred.loc)

          //inhale nested-relation
          val params: Seq[TypeVar] = program.findDomain(nestedFunc.get.domainName).typVars
          val types: Seq[Type] =
            Seq(DomainType(PredicateInstanceDomain.get, ListMap()), DomainType(PredicateInstanceDomain.get, ListMap()), Int)

          val mapNested: ListMap[TypeVar, Type] = ListMap(params.zip(types):_*)
          val inhale = Inhale(DomainFuncApp(nestedFunc.get,
            Seq(varOfCalleePred.localVar, varOfCallerPred.localVar),
            mapNested)(calledPred.pos))(calledPred.pos)
          Seqn(Seq(assign, inhale), Seq(varOfCalleePred))(calledPred.pos)
        case mw: MagicWand =>
          sys.error(s"Unexpectedly found resource access node $mw")
      }
      case c: CondExp =>
        val thn = transformPredicateBody(c.thn, unfoldedPredVar, unfoldPermission)
        val els = transformPredicateBody(c.els, unfoldedPredVar, unfoldPermission)
        If(c.cond, Seqn(Seq(thn), Nil)(c.pos), Seqn(Seq(els), Nil)(c.pos))(c.pos)
      case i: Implies =>
        val thn = transformPredicateBody(i.right, unfoldedPredVar, unfoldPermission)
        If(i.left, Seqn(Seq(thn), Nil)(i.pos), EmptyStmt)(i.pos)
      case b: BinExp =>
        val left = transformPredicateBody(b.left, unfoldedPredVar, unfoldPermission)
        val right = transformPredicateBody(b.right, unfoldedPredVar, unfoldPermission)
        Seqn(Seq(left, right), Nil)(b.pos)
      case u: UnExp => transformPredicateBody(u.exp, unfoldedPredVar, unfoldPermission)
      case _ => EmptyStmt
    }
  }

  /**
    * Generates for a predicate and a variable the corresponding assignment
    * it generates the viper-representation of a predicate (via loc-domain and the proper domain-function)
    * and assign it to the given value
    *
    * @param pred        the predicate which defines the predicate-Domain and predicate-domainFunc
    * @param assLocation the variable, which should be assigned
    * @return an assignment of the given variable to the representation of a predicate with the corresponding arguments
    */
  protected def generatePredicateAssign(assLocation: LocalVar, pred: PredicateAccess)
                              : LocalVarAssign = {
    val pi = PredicateInstance(pred.args, pred.predicateName)(pred.pos, pred.info, pred.errT)
    LocalVarAssign(assLocation, pi)(pred.pos)
  }


  /**
    * Generator of the predicate-variables, which represents the type 'predicate'.
    * locationDomain must be defined!
    * @param p predicate which defines the type of the variable
    * @return a local variable with the correct type
    */
  protected def uniquePredicateInstanceVar(p: PredicateAccess): LocalVarDecl = {
    assert(PredicateInstanceDomain.isDefined)
    val predName = p.predicateName + "_" + p.args.hashCode().toString.replaceAll("-", "_")
    val predVarName = uniqueLocalVar(predName)
    val info = SimpleInfo(Seq(p.predicateName + "_" + p.args.mkString(",")))
    val newLocalVar =
      LocalVarDecl(predVarName, PredicateInstance.getType)(info = info)
    newLocalVar
  }

  private val usedPredicateInstanceVariables: collection.mutable.Set[String] = collection.mutable.Set[String]()

  //TODO: assumed that pred variable names are alone in the proof method.
  private def uniqueLocalVar(name: String): String = {
    var i = 0
    var newName = name
    while(usedPredicateInstanceVariables.contains(newName)){
      newName = name + i
      i += 1
    }
    usedPredicateInstanceVariables.add(newName)
    newName
  }

  def reportNestedNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("nestedPredicates function is needed but not declared.", pos))
  }

  def reportPredicateInstanceNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("PredicateInstance domain is needed but not declared.", pos))
  }
}