package silAST.programs {

import silAST.source.SourceLocation
import silAST.types.{NonReferenceDataType, DataType}
import collection.mutable.{HashSet, HashMap}
import silAST.symbols._
import silAST.expressions._
import silAST.domains.{DomainPredicate, DomainFactory}
import silAST.expressions.util.{DTermSequence, PTermSequence, TermSequence}
import terms.{GeneralTerm, DomainTerm, Term, ProgramTerm}
import silAST.ASTNode

final class ProgramFactory(
                            val name: String
                            ) {

  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(
                              sl: SourceLocation,
                              t1: Term,
                              t2: Term
                              ): EqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case (t1: ProgramTerm, t2: ProgramTerm) => makePEqualityExpression(sl,t1,t2)
      case (t1: DomainTerm, t2: DomainTerm)   => makeDEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new EqualityExpression(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(sl: SourceLocation,t1: ProgramTerm,t2: ProgramTerm) : PEqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new PEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDEqualityExpression(sl: SourceLocation,t1: DomainTerm,t2: DomainTerm) : DEqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression[DEqualityExpression]( new DEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGEqualityExpression(
                              sl: SourceLocation,
                              t1: GeneralTerm,
                              t2: GeneralTerm
                              ): GEqualityExpression =
  {
    require(terms.contains(t1))
    require(terms.contains(t2))
    addExpression ( new GEqualityExpression(sl, t1, t2) )
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private def addExpression[E <: Expression](e: E)  : E = {
    expressions + e
    nodeMap += e.sourceLocation -> e
    e
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val domainPredicates = new HashMap[String, DomainPredicate]

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val terms = new HashSet[Term]
  private val expressions = new HashSet[Expression]

  private val nodeMap = new HashMap[SourceLocation,ASTNode]

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getDomainFactory(name: String): DomainFactory =
    domainFactories.getOrElseUpdate(name, new DomainFactory(this, name))

  //////////////////////////////////////////////////////////////////////////
  def getMethodFactory(name: String): MethodFactory =
    methodFactories.getOrElseUpdate(name, new MethodFactory(this, name))

  //////////////////////////////////////////////////////////////////////////
  def defineDomainField(sl: SourceLocation, name: String, dataType: NonReferenceDataType): Field = {
    require(dataTypes.contains(dataType))
    defineField(new NonReferenceField(sl, name, dataType))
  }

  //////////////////////////////////////////////////////////////////////////
  def defineReferenceField(sl: SourceLocation, name: String): Field = {
    defineField(new ReferenceField(sl, name))
  }

  //////////////////////////////////////////////////////////////////////////
  //@Symbol construction
  //////////////////////////////////////////////////////////////////////////

  def defineField(field: Field): Field = {
    require(!fields.contains(field.name))

    fields += (field.name -> field)

    field
  }

  //////////////////////////////////////////////////////////////////////////
  def defineDataTypeSequence(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    dataTypeSequences.getOrElseUpdate(types, new DataTypeSequence(types))
  }

  //////////////////////////////////////////////////////////////////////////
  def defineFunctionSignature(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    dataTypeSequences.getOrElseUpdate(types, new DataTypeSequence(types))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val domainFactories = new HashMap[String, DomainFactory]
  private val methodFactories = new HashMap[String, MethodFactory]

  private val fields = new HashMap[String, Field]
  private val dataTypes = new HashSet[DataType]

  private val dataTypeSequences = new HashMap[List[DataType], DataTypeSequence]
}

}


