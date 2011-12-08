package silAST.methods.implementations

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.PTermSequence
import collection.Set
import collection.mutable.HashSet
import silAST.methods.MethodFactory
import silAST.expressions.{PredicateExpression, PExpression, Expression, ExpressionFactory}
import silAST.expressions.terms.PTerm
import silAST.expressions.terms.permission.PermissionVariable


class BasicBlockFactory private[silAST](
                                         private val implementationFactory: ImplementationFactory,
                                         val sl: SourceLocation,
                                         val name: String
                                         ) extends NodeFactory with ExpressionFactory {
  //////////////////////////////////////////////////////////////////
  def compile(): BasicBlock = {
    basicBlock
  }

  //////////////////////////////////////////////////////////////////
  def appendAssignment(
                        sl: SourceLocation,
                        target: ProgramVariable,
                        source: PTerm
                        ) = {
    require(localVariables.contains(target) || results.contains(target)) //no writing to inputs
    require(terms contains source)
    basicBlock.appendStatement(new Assignment(sl, target, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendFieldAssignment(
                             sl: SourceLocation,
                             target: ProgramVariable,
                             field: Field,
                             source: PExpression
                             ) {
    require(programVariables.contains(target))
    require(fields.contains(field))
    require(expressions.contains(source))

    basicBlock.appendStatement(new FieldAssignment(sl, target, field, source))
  }

  //////////////////////////////////////////////////////////////////
  def appendNewStatement(
                          sl: SourceLocation,
                          target: ProgramVariable,
                          dataType: DataType
                          ) {
    require(localVariables.contains(target))
    require(dataTypes.contains(dataType))

    basicBlock.appendStatement(new NewStatement(sl, target, dataType))
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(sl: SourceLocation, vs: Seq[ProgramVariable]): ProgramVariableSequence = {
    require(vs.forall(programVariables.contains(_)))
    val result = new ProgramVariableSequence(sl, vs)
    programVariableSequences += result
    result
  }

  //////////////////////////////////////////////////////////////////
  def appendCallStatement(
                           sl: SourceLocation,
                           targets: ProgramVariableSequence,
                           receiver: PExpression,
                           methodFactory: MethodFactory,
                           arguments: PTermSequence
                           ) {
    require(programVariableSequences contains targets)
    require(targets.forall(localVariables contains _))
    require(expressions contains receiver)
    require(methodFactories contains methodFactory)
    require(arguments.forall( terms contains _))

    basicBlock.appendStatement(new CallStatement(sl, targets, receiver, methodFactory.method, arguments))
  }

  //////////////////////////////////////////////////////////////////
  def appendInhale(
                    sl: SourceLocation,
                    e: Expression
                    ) {
    require(expressions.contains(e))

    basicBlock.appendStatement(new Inhale(sl, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendExhale(
                    sl: SourceLocation,
                    e: Expression
                    ) {
    require(expressions.contains(e))

    basicBlock.appendStatement(new Exhale(sl, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendFold(
                  sl: SourceLocation,
                  e: PredicateExpression
                  ) {
    require(expressions.contains(e))

    basicBlock.appendStatement(new Fold(sl, e))
  }

  //////////////////////////////////////////////////////////////////
  def appendUnfold(
                    sl: SourceLocation,
                    e: PredicateExpression
                    ) {
    require(expressions.contains(e))

    basicBlock.appendStatement(new Unfold(sl, e))
  }

  //////////////////////////////////////////////////////////////////
  def addSuccessor(sl: SourceLocation, successor: BasicBlockFactory, condition: Expression, isBackEdge: Boolean) = {
    require(basicBlock.successors.forall(_.target != successor.basicBlock))
    new CFGEdge(sl, basicBlock, successor.basicBlock, condition, isBackEdge)
  }

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  override def fields: Set[Field] = implementationFactory.fields

  def localVariables = implementationFactory.localVariables

  def results = implementationFactory.results

  private def parameters = implementationFactory.parameters

  private def methodFactories = implementationFactory.methodFactories

  override def programVariables: Set[ProgramVariable] =
    localVariables.toSet[ProgramVariable] union parameters.toSet[ProgramVariable]

  override def functions = implementationFactory.functions

  val programVariableSequences = new HashSet[ProgramVariableSequence]


  override protected[silAST] def predicates = implementationFactory.predicates

  override protected[silAST] def domainFunctions = implementationFactory.domainFunctions

  override protected[silAST] def domainPredicates = implementationFactory.domainPredicates

  override val nullFunction = implementationFactory.nullFunction

  override def trueExpression = implementationFactory.trueExpression

  override def falseExpression = implementationFactory.falseExpression

  protected[silAST] override def dataTypes = implementationFactory.dataTypes union pDataTypes

  protected[silAST] override def domainFactories = implementationFactory.domainFactories
  protected[silAST] override def permissionVariables  : collection.Set[PermissionVariable] = implementationFactory.permissionVariables

  private[silAST] val basicBlock: BasicBlock = new BasicBlock(sl, name, implementationFactory.cfg)
}