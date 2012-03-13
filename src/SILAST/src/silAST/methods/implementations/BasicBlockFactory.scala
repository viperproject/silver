package silAST.methods.implementations

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.PTermSequence
import collection.Set
import silAST.methods.MethodFactory
import silAST.expressions.{PredicateExpression, PExpression, Expression, ExpressionFactory}
import silAST.expressions.terms.PTerm
import silAST.programs.ScopeFactory
import collection.mutable.{ListBuffer, HashSet}


class BasicBlockFactory private[silAST](
                                         private val implementationFactory: ImplementationFactory,
                                         val sourceLocation : SourceLocation,
                                         val name: String
                                         ) extends NodeFactory with ExpressionFactory with ScopeFactory {
  //////////////////////////////////////////////////////////////////
  def compile(): BasicBlock = {
    basicBlock.cfg = implementationFactory.cfg
    basicBlock
  }

  //////////////////////////////////////////////////////////////////
  def addProgramVariableToScope(v : ProgramVariable)
  {
    require (!(localVariables contains v))
    require( implementationFactory.localVariables contains v)
    basicBlock.pLocalVariables.append(v)
  }

  //////////////////////////////////////////////////////////////////
  def appendAssignment(
                        sourceLocation : SourceLocation,
                        target: ProgramVariable,
                        source: PTerm
                        ) = {
    require((localVariables contains target)  || (results contains target)) //no writing to inputs

    migrate(source)
    basicBlock.appendStatement(new AssignmentStatement(sourceLocation, target, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendFieldAssignment(
                             sourceLocation : SourceLocation,
                             target: ProgramVariable,
                             field: Field,
                             source: PTerm
                             ) {
    require(programVariables contains target)
    require(fields contains field)

    migrate(source)
    
    basicBlock.appendStatement(new FieldAssignmentStatement(sourceLocation, target, field, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendNew(
                          sourceLocation : SourceLocation,
                          target: ProgramVariable,
                          dataType: DataType
                          ) {
    require(localVariables contains target)
    require(dataTypes contains dataType)

    basicBlock.appendStatement(new NewStatement(sourceLocation, target, dataType))
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(sourceLocation : SourceLocation, vs: Seq[ProgramVariable]): ProgramVariableSequence = {
    require(vs.forall(programVariables contains _))
    val result = new ProgramVariableSequence(sourceLocation, vs)
    programVariableSequences += result
    result
  }

  //////////////////////////////////////////////////////////////////
  def appendCall(
                           sourceLocation : SourceLocation,
                           targets: ProgramVariableSequence,
                           receiver: PTerm,
                           methodFactory: MethodFactory,
                           arguments: PTermSequence
                           ) {
    require(programVariableSequences contains targets)
    require(targets.forall(localVariables contains _))
    require(methodFactories contains methodFactory)

    migrate(receiver)
    arguments foreach migrate 
    
    basicBlock.appendStatement(new CallStatement(sourceLocation, targets, receiver, methodFactory.method, arguments))
  }

  //////////////////////////////////////////////////////////////////
  def appendInhale(
                    sourceLocation : SourceLocation,
                    e: Expression
                    ) {
    migrate(e)

    basicBlock.appendStatement(new InhaleStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendExhale(
                    sourceLocation : SourceLocation,
                    e: Expression
                    ) {
    migrate(e)

    basicBlock.appendStatement(new ExhaleStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendFold(
                  sourceLocation : SourceLocation,
                  e: PredicateExpression
                  ) {
    migrate(e)

    basicBlock.appendStatement(new FoldStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendUnfold(
                    sourceLocation : SourceLocation,
                    e: PredicateExpression
                    ) {
    migrate(e)

    basicBlock.appendStatement(new UnfoldStatement(sourceLocation, e))
  }

  //////////////////////////////////////////////////////////////////
  def addSuccessor(sourceLocation : SourceLocation, successor: BasicBlockFactory, condition: Expression, isBackEdge: Boolean = false) = {
    require(basicBlock.successors.forall(_.target != successor.basicBlock))
    new CFGEdge(sourceLocation, basicBlock, successor.basicBlock, condition, isBackEdge)
  }

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  override val parentFactory = Some(implementationFactory)
  
  override def fields: Set[Field] = implementationFactory.fields

//  private val scopedVariables = new ListBuffer[ProgramVariable];

  def localVariables = basicBlock.localVariables; //scopedVariables;

  def results = implementationFactory.results

  private def parameters = implementationFactory.parameters

  override def programVariables: Set[ProgramVariable] =
    localVariables union parameters.toSet[ProgramVariable]

//  override def functions = implementationFactory.functions

  val programVariableSequences = new HashSet[ProgramVariableSequence]

  override def dataTypes = implementationFactory.dataTypes union pDataTypes

  override def typeVariables = Set()

  private[silAST] lazy val basicBlock: BasicBlock = new BasicBlock(sourceLocation, name)
}