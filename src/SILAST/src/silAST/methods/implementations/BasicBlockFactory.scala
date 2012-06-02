package silAST.methods.implementations

import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.expressions.util.PTermSequence
import collection.Set
import silAST.expressions.{Expression, ExpressionFactory}
import silAST.methods.{Scope, MethodFactory}
import silAST.programs.NodeFactory
import silAST.programs.symbols.{PredicateFactory, ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.terms.{PredicateLocation, Term, PTerm}


class BasicBlockFactory private[silAST]
(
  val cfg: ControlFlowGraph,

  override val name: String
  )(override val sourceLocation: SourceLocation,comment : List[String])
  extends BlockFactory(cfg.scope, name)(sourceLocation,comment)
  with NodeFactory
  with ExpressionFactory {
  //////////////////////////////////////////////////////////////////
  override type B = BasicBlock

  //////////////////////////////////////////////////////////////////
  override val scope: Scope = cfg.scope

  //////////////////////////////////////////////////////////////////
  override def compile(): BasicBlock = {
    block
  }

  //////////////////////////////////////////////////////////////////
  def appendCall(
                  targets: ProgramVariableSequence,
                  receiver: PTerm,
                  methodFactory: MethodFactory,
                  arguments: PTermSequence,
                  sourceLocation: SourceLocation,comment : List[String] = Nil) {
    require(programVariableSequences contains targets)
    require(targets.forall(programVariables contains _))
    require(scope.factory.methodFactories contains methodFactory)

    migrateP(receiver)
    arguments foreach migrateP

    block.appendStatement(new CallStatement(targets, methodFactory.method, PTermSequence(receiver :: arguments.toList: _*))
      (sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendInhale(
                    e: Expression,
                    sourceLocation: SourceLocation,
                    comment : List[String] = Nil) {
    migrate(e)

    block.appendStatement(new InhaleStatement(e)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendExhale(

                    e: Expression,
                    sourceLocation: SourceLocation) {
    appendExhale(e,None,sourceLocation)
  }

  def appendExhale(e:Expression, message : Option[String],sourceLocation:SourceLocation,comment : List[String] = Nil){
    migrate(e)

    block.appendStatement(new ExhaleStatement(e,message)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendFold(
                  r : Term,
                  pf : PredicateFactory,
                  perm : Term,
                  sourceLocation: SourceLocation,
                  comment : List[String] = Nil) {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(perm)

    block.appendStatement(new FoldStatement(new PredicateLocation(r,pf.pPredicate),perm)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendUnfold(
                    r : Term,
                    pf : PredicateFactory,
                    perm : Term,
                    sourceLocation: SourceLocation,
                    comment : List[String] = Nil) {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(perm)

    block.appendStatement(new UnfoldStatement(new PredicateLocation(r,pf.pPredicate),perm)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  private def writableVariables =
    programVariables diff block.implementation.method.signature.parameters.toSet

  //////////////////////////////////////////////////////////////////
  def appendAssignment(
                        target: ProgramVariable,
                        source: PTerm
                        ,sourceLocation: SourceLocation,comment : List[String] = Nil) = {
    require(writableVariables contains target) //no writing to inputs

    migrateP(source)
    block.appendStatement(new AssignmentStatement(target, source)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendFieldAssignment(
                             target: ProgramVariable,
                             field: Field,
                             source: PTerm
                             ,sourceLocation: SourceLocation,
                             comment : List[String] = Nil) {
    require(programVariables contains target)
    require(fields contains field)

    migrateP(source)

    block.appendStatement(new FieldAssignmentStatement(target, field, source)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  def appendNew(
                 target: ProgramVariable,
                 dataType: DataType,
                 sourceLocation: SourceLocation,
                 comment : List[String] = Nil) {
    require(writableVariables contains target)
    require(scope.factory.dataTypes contains dataType)

    block.appendStatement(new NewStatement(target, dataType)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  override def programVariables = scope.programVariables

  override def inputProgramVariables = scope.factory.inputProgramVariables

  override def outputProgramVariables = scope.factory.outputProgramVariables

  override def predicates = scope.factory.predicates

  override def functions = scope.factory.functions

  override def domainFunctions = scope.factory.domainFunctions

  override def domainPredicates = scope.factory.domainPredicates

  override protected[silAST] def domainFactories = scope.factory.domainFactories

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  val parentFactory = Some(scope.factory)

  override def fields: Set[Field] = scope.factory.fields

  override def dataTypes = scope.factory.dataTypes

  override def typeVariables = Set()

  override val block: BasicBlock = new BasicBlock(cfg, scope, name, this)(sourceLocation,comment)

}