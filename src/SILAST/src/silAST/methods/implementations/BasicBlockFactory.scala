package silAST.methods.implementations

import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.PTermSequence
import collection.Set
import silAST.expressions.{PredicateExpression, Expression, ExpressionFactory}
import silAST.expressions.terms.PTerm
import silAST.methods.{Scope, MethodFactory}
import silAST.programs.NodeFactory


class BasicBlockFactory private[silAST]
  (
    val cfg : ControlFlowGraph,
    override val sourceLocation: SourceLocation,
    override val name: String
  )
  extends BlockFactory(cfg.scope,sourceLocation,name)
  with NodeFactory
  with ExpressionFactory
{
  //////////////////////////////////////////////////////////////////
  override type B = BasicBlock

  //////////////////////////////////////////////////////////////////
  override val scope : Scope = cfg.scope

  //////////////////////////////////////////////////////////////////
  override def compile(): BasicBlock = {
    block
  }

  //////////////////////////////////////////////////////////////////
  def appendCall(
                  sourceLocation: SourceLocation,
                  targets: ProgramVariableSequence,
                  receiver: PTerm,
                  methodFactory: MethodFactory,
                  arguments: PTermSequence
                  )
  {
    require(programVariableSequences contains targets)
    require(targets.forall(programVariables contains _))
    require(scope.factory.methodFactories contains methodFactory)

    migrate(receiver)
    arguments foreach migrate

    block.appendStatement(new CallStatement(sourceLocation, targets, receiver, methodFactory.method, arguments))
  }

  //////////////////////////////////////////////////////////////////
  def appendInhale(
                    sourceLocation: SourceLocation,
                    e: Expression
                    ) {
    migrate(e)

    block.appendStatement(new InhaleStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendExhale(
                    sourceLocation: SourceLocation,
                    e: Expression
                    ) {
    migrate(e)

    block.appendStatement(new ExhaleStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendFold(
                  sourceLocation: SourceLocation,
                  e: PredicateExpression
                  ) {
    migrate(e)

    block.appendStatement(new FoldStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendUnfold(
                    sourceLocation: SourceLocation,
                    e: PredicateExpression
                    ) {
    migrate(e)

    block.appendStatement(new UnfoldStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  private def writableVariables =
    programVariables diff block.implementation.method.signature.parameters.toSet

  //////////////////////////////////////////////////////////////////
  def appendAssignment(
                        sourceLocation: SourceLocation,
                        target: ProgramVariable,
                        source: PTerm
                        ) = {
    require(writableVariables contains target ) //no writing to inputs

    migrate(source)
    block.appendStatement(new AssignmentStatement(sourceLocation, target, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendFieldAssignment(
                             sourceLocation: SourceLocation,
                             target: ProgramVariable,
                             field: Field,
                             source: PTerm
                             ) {
    require(programVariables contains target)
    require(fields contains field)

    migrate(source)

    block.appendStatement(new FieldAssignmentStatement(sourceLocation, target, field, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendNew(
                 sourceLocation: SourceLocation,
                 target: ProgramVariable,
                 dataType: DataType
                 ) {
    require(writableVariables contains target)
    require(scope.factory.dataTypes contains dataType)

    block.appendStatement(new NewStatement(sourceLocation, target, dataType))
  }
/*
  //////////////////////////////////////////////////////////////////
  override def makeProgramVariableSequence(sourceLocation: SourceLocation, vs: Seq[ProgramVariable]): ProgramVariableSequence = {
    require(vs.forall(programVariables contains _))
    val result = new ProgramVariableSequence(sourceLocation, vs)
    programVariableSequences += result
    result
  }
  */

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
//  override def dataTypes = scope.factory.dataTypes
  override def programVariables = scope.programVariables
  override def predicates = scope.factory.predicates
  override def functions  = scope.factory.functions
  override def domainFunctions  = scope.factory.domainFunctions
  override def domainPredicates = scope.factory.domainPredicates
//  override def typeVariables  = scope.factory.typeVariables
  override protected[silAST] def domainFactories = scope.factory.domainFactories

 //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  val parentFactory = Some(scope.factory)

  override def fields: Set[Field] = scope.factory.fields

//  def results = implementationFactory.results

//  private def parameters = block.implementation.factory.parameters

//  override def programVariables: collection.Set[ProgramVariable] = scope.programVariables.toSet[ProgramVariable]

  override def dataTypes = scope.factory.dataTypes

  override def typeVariables = Set()

  override val block : BasicBlock = new BasicBlock(cfg,scope,name,this)(sourceLocation)
}