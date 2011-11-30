package silAST.programs
{

import silAST.domains.DomainFactory
import silAST.source.SourceLocation
import silAST.types.{NonReferenceDataType, DataType}
import collection.mutable.{HashSet, HashMap}
import silAST.symbols._
import silAST.expressions._
import terms.{DomainTerm, Term, ProgramTerm}

final class ProgramFactory(
    val name : String
  )
  {
    //////////////////////////////////////////////////////////////////////////
    private def addExpression[E <: Expression](
      map : HashMap[String,E],
      stringRep : String,
      make : => E
    ) : E = map.getOrElseUpdate(stringRep,make)
    
    //////////////////////////////////////////////////////////////////////////
    private def addSpecializedExpression[SE <: Expression, PE <: E with SE,E <: Expression](
      pMap : HashMap[String,PE],
      map : HashMap[String,E],
      stringRep : String,
      make :  => PE
    ) : PE = 
    {
      val result = pMap.getOrElseUpdate(stringRep,make)
      map.update(stringRep,result)
      expressions.update(stringRep,result)
      result
    }

    //////////////////////////////////////////////////////////////////////////
    private def addProgramExpression[PE <: E with ProgramExpression,E  <: Expression](
      pMap : HashMap[String,PE],
      map : HashMap[String,E],
      stringRep : String,
      make :  => PE
    ) : PE = addSpecializedExpression[ProgramExpression,PE,E](pMap,map,stringRep,make)

    //////////////////////////////////////////////////////////////////////////
    private def addDomainExpression[DE <: E with DomainExpression,E  <: Expression](
      dMap : HashMap[String,DE],
      map : HashMap[String,E],
      stringRep : String,
      make :  => DE
    ) : DE = addSpecializedExpression[DomainExpression,DE,E](dMap,map,stringRep,make)

    //////////////////////////////////////////////////////////////////////////
    def makePEqualityExpression(
       sl : SourceLocation, 
       pTerm1 : ProgramTerm, 
       pTerm2 : ProgramTerm
    ) : PEqualityExpression = 
    {
      require(programTerms.contains(pTerm1))
      require(programTerms.contains(pTerm2))
      addProgramExpression(
        pEqualityExpressions,
        equalityExpressions, 
        List(sl, pTerm1, pTerm2).toString(),
        new PEqualityExpression(sl,pTerm1,pTerm2)
      )
    }
    
    //////////////////////////////////////////////////////////////////////////
    def makeDEqualityExpression(
       sl : SourceLocation, 
       dTerm1 : DomainTerm, 
       dTerm2 : DomainTerm
    ) : DEqualityExpression = 
    {
      require(domainTerms.contains(dTerm1))
      require(domainTerms.contains(dTerm2))
      addDomainExpression[DEqualityExpression,EqualityExpression](
        dEqualityExpressions,
        equalityExpressions, 
        List(sl, dTerm1, dTerm2).mkString("|"),
        new DEqualityExpression(sl,dTerm1,dTerm2)
      )
    }

    //////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////
    private val programTerms = new HashSet[ProgramTerm]
    private val  domainTerms = new HashSet[DomainTerm]
    

    private val dEqualityExpressions = new HashMap[String,DEqualityExpression]
    private val pEqualityExpressions = new HashMap[String,PEqualityExpression]
    private val  equalityExpressions = new HashMap[String,EqualityExpression]
    
    private val dDomainPredicateExpressions = new HashMap[String,DDomainPredicateExpression]
    private val pDomainPredicateExpressions = new HashMap[String,PDomainPredicateExpression]
    private val  domainpredicateExpressions = new HashMap[String,DomainPredicateExpression]

    private val dUnaryBooleanExpressions = new HashMap[String,DUnaryBooleanExpression]
    private val pUnaryBooleanExpressions = new HashMap[String,PUnaryBooleanExpression]
    private val  unaryBooleanExpressions = new HashMap[String, UnaryBooleanExpression]

    private val dBinaryBooleanExpressions = new HashMap[String,DBinaryBooleanExpression]
    private val pBinaryBooleanExpressions = new HashMap[String,PBinaryBooleanExpression]
    private val  binaryBooleanExpressions = new HashMap[String, BinaryBooleanExpression]

    private val accessPermissionExpressions = new HashMap[String,AccessPermissionExpression]
    private val unfoldingExpressions = new HashMap[String,UnfoldingExpression]

    private val pPredicateExpressions = new HashMap[String,PPredicateExpression]
    private val  predicateExpressions = new HashMap[String,PredicateExpression]

    private val dQuantifierExpressions = new HashMap[String,DQuantifierExpression]
    private val quantifierExpressions = new HashMap[String,QuantifierExpression]

    private val expressions          = new HashMap[String,Expression]
/*    
    //////////////////////////////////////////////////////////////////////////
    def makeEqualityExpression(
      sl : SourceLocation,
      term1: Term,
      term2: Term
    ): EqualityExpression =
    {
      require(terms.contains(term1))
      require(terms.contains(term2))

      expressions.
    }
  */
    //////////////////////////////////////////////////////////////////////////
    def getDomainFactory(name : String) : DomainFactory =
      domainFactories.getOrElseUpdate(name, new DomainFactory(this,name))

    //////////////////////////////////////////////////////////////////////////
    def getMethodFactory(name : String) : MethodFactory =
      methodFactories.getOrElseUpdate(name,new MethodFactory(this,name))

    //////////////////////////////////////////////////////////////////////////
    def defineDomainField(sl : SourceLocation, name : String, dataType : NonReferenceDataType) : Field = {
      require(dataTypes.contains(dataType))
      defineField(new NonReferenceField(sl,name,dataType))
    }

    //////////////////////////////////////////////////////////////////////////
    def defineReferenceField(sl : SourceLocation, name : String) : Field = {
      defineField(new ReferenceField(sl,name))
    }

    //////////////////////////////////////////////////////////////////////////
    //@Symbol construction
    //////////////////////////////////////////////////////////////////////////

    def defineField(field : Field) : Field = {
      require(!fields.contains(field.name))

      fields += (field.name -> field)

      field
    }

    //////////////////////////////////////////////////////////////////////////
    def defineDataTypeSequence(types : List[DataType]) : DataTypeSequence = {
      require(types.forall(dataTypes.contains(_)))

      dataTypeSequences.getOrElseUpdate(types,new DataTypeSequence(types))
    }

    //////////////////////////////////////////////////////////////////////////
    def defineFunctionSignature(types : List[DataType]) : DataTypeSequence = {
      require(types.forall(dataTypes.contains(_)))

      dataTypeSequences.getOrElseUpdate(types,new DataTypeSequence(types))
    }

    //////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////
    private val domainFactories = new HashMap[String,DomainFactory]
    private val methodFactories = new HashMap[String,MethodFactory]

    private val fields = new HashMap[String,Field]
    private val dataTypes = new HashSet[DataType]

    private val dataTypeSequences = new HashMap[List[DataType],DataTypeSequence]
  }
}


