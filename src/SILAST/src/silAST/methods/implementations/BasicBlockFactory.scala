package silAST.methods.implementations

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.PTermSequence
import collection.Set
import collection.mutable.{HashSet, HashMap, ListBuffer}
import silAST.methods.{MethodFactory}
import silAST.expressions.{PredicateExpression, PExpression, Expression, ExpressionFactory}


class BasicBlockFactory private[silAST](
    private val implementationFactory : ImplementationFactory,
    val sl : SourceLocation,
    val name : String
  ) extends NodeFactory with ExpressionFactory
{
  //////////////////////////////////////////////////////////////////
  def appendAssignment(
      sl: SourceLocation,
      target: ProgramVariable,
      source: PExpression
  ) {
    require(localVariables.contains(target) || results.contains(target)) //no writing to inputs
    require(expressions.contains(source))
    statements += new Assignment(sl,target,source)
  }

  //////////////////////////////////////////////////////////////////
  def appendFieldAssignment(
      sl: SourceLocation,
      target: ProgramVariable,
      field : Field,
      source: PExpression
  ) {
    require(programVariables.contains(target))
    require(fields.contains(field))
    require(expressions.contains(source))

    statements += new FieldAssignment(sl,target,field,source)
  }

  //////////////////////////////////////////////////////////////////
  def appendNewStatement(
      sl: SourceLocation,
      target: ProgramVariable,
      dataType : DataType
  ) {
    require(localVariables.contains(target))
    require(dataTypes.contains(dataType))

    statements += new NewStatement(sl,target,dataType)
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(sl : SourceLocation, vs : Seq[ProgramVariable]) : ProgramVariableSequence = {
    require(vs.forall(programVariables.contains(_)))
    val result = new ProgramVariableSequence(sl,vs)
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
    require(programVariableSequences.contains(targets))
    require(targets.forall(localVariables.contains(_)))
    require(expressions.contains(receiver))
    require(methodFactories.contains(methodFactory))
    require(termSequences.contains(arguments))

    statements += new CallStatement(sl,targets, receiver,methodFactory.method,arguments)
  }

  //////////////////////////////////////////////////////////////////
  def appendInhale(
                           sl: SourceLocation,
                           e : Expression
  ) {
    require(expressions.contains(e))

    statements += new Inhale(sl,e)
  }

  //////////////////////////////////////////////////////////////////
  def appendExhale(
                           sl: SourceLocation,
                           e : Expression
  )
  {
    require(expressions.contains(e))

    statements += new Exhale(sl,e)
  }

  //////////////////////////////////////////////////////////////////
  def appendFold(
                           sl: SourceLocation,
                           e : PredicateExpression
  )
  {
    require(expressions.contains(e))

    statements += new Fold(sl,e)
  }

  //////////////////////////////////////////////////////////////////
  def appendUnfold(
                           sl: SourceLocation,
                           e : PredicateExpression
  )
  {
    require(expressions.contains(e))

    statements += new Unfold(sl,e)
  }

  //////////////////////////////////////////////////////////////////
  def addSuccessor( sl : SourceLocation, successor : BasicBlockFactory, condition : Expression ) = {
    require(!successors.contains(successor))
    successors += successor -> (sl,condition)
  }

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
  val statements = new ListBuffer[Statement]
  val successors = new HashMap[BasicBlockFactory, (SourceLocation, Expression)]

  override def fields : Set[Field] = implementationFactory.fields
  def localVariables = implementationFactory.localVariables
  def results        = implementationFactory.results
  private def parameters      = implementationFactory.parameters
  private val methodFactories = implementationFactory.methodFactories

  override def programVariables : Set[ProgramVariable] = localVariables union parameters.toSet
  override def functions = implementationFactory.functions
  val programVariableSequences = new HashSet[ProgramVariableSequence]
}