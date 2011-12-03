package silAST.programs {

import silAST.source.SourceLocation
import silAST.types.{NonReferenceDataType, DataType}
import collection.mutable.{HashSet, HashMap}
import silAST.symbols._
import silAST.expressions._
import silAST.domains.{DomainPredicate, DomainFactory}
import terms.{DomainTerm, Term, ProgramTerm}
import silAST.expressions.util.{DTermSequence, PTermSequence, TermSequence}

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
      case (t1: ProgramTerm, t2: ProgramTerm) =>
        addSpecializedExpression[ProgramExpression, PEqualityExpression, EqualityExpression](pEqualityExpressions, equalityExpressions, eKey(sl, t1, t2), new PEqualityExpression(sl, t1, t2))
      case (t1: DomainTerm, t2: DomainTerm) =>
        addSpecializedExpression[DomainExpression, DEqualityExpression, EqualityExpression](dEqualityExpressions, equalityExpressions, eKey(sl, t1, t2), new DEqualityExpression(sl, t1, t2))
      case _ => addExpression(equalityExpressions, eKey(sl, t1, t2), new EqualityExpression(sl, t1, t2))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  private def eKey(nodes: Any*): String
  = nodes.mkString("|")

  /*
    //////////////////////////////////////////////////////////////////////////
    private[silAST] def makePEqualityExpression(
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
        List(sl, pTerm1, pTerm2).mkString("|"),
        new PEqualityExpression(sl,pTerm1,pTerm2)
      )
    }
    
    //////////////////////////////////////////////////////////////////////////
    private[silAST] def makeDEqualityExpression(
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
    private def dpeKey( sl : SourceLocation, p : DomainPredicate, a : TermSequence) =
      List(sl,p,a).mkString("|")
  */
  //////////////////////////////////////////////////////////////////////////

  private def makePDomainPredicateExpression(sl: SourceLocation, p: DomainPredicate, a: PTermSequence): PDomainPredicateExpression = {
    require(domainPredicates.get(p.name) equals p)
    require(a.forall(programTerms.contains(_)))

    val result = pDomainPredicateExpressions.getOrElseUpdate(eKey(sl, p, a), new PDomainPredicateExpression(sl, p, a))
    domainPredicateExpressions += (eKey(sl, p, a) -> result)
    result
  }

  //////////////////////////////////////////////////////////////////////////

  private def makeDDomainPredicateExpression(sl: SourceLocation, p: DomainPredicate, a: DTermSequence): DDomainPredicateExpression = {
    require(domainPredicates.get(p.name) equals p)
    require(a.forall(domainTerms.contains(_)))

    val result = dDomainPredicateExpressions.getOrElseUpdate(eKey(sl, p, a), new DDomainPredicateExpression(sl, p, a))
    domainPredicateExpressions += (eKey(sl, p, a) -> result)
    result
  }

  //
  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(
                                     sl: SourceLocation,
                                     predicate: DomainPredicate,
                                     arguments: TermSequence
                                     ): DomainPredicateExpression = {
    require(domainPredicates.get(predicate.name) equals predicate)
    require(arguments.forall(terms.contains(_)))
    arguments match {
      case x: PTermSequence => makePDomainPredicateExpression(sl, predicate, x)
      case x: DTermSequence => makeDDomainPredicateExpression(sl, predicate, x)
      case _ => {
        val result = domainPredicateExpressions.getOrElseUpdate(
          eKey(sl, predicate, arguments),
          new DomainPredicateExpression(sl, predicate, arguments)
        )
        expressions += (eKey(sl, predicate, arguments) -> result)
        result
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private def addExpression[E <: Expression](
                                              map: HashMap[String, E],
                                              stringRep: String,
                                              make: => E
                                              ): E = map.getOrElseUpdate(stringRep, make)

  //////////////////////////////////////////////////////////////////////////
  private def addSpecializedExpression[SE <: Expression, PE <: E with SE, E <: Expression](
                                                                                            pMap: HashMap[String, PE],
                                                                                            map: HashMap[String, E],
                                                                                            stringRep: String,
                                                                                            make: => PE
                                                                                            ): PE = {
    val result = pMap.getOrElseUpdate(stringRep, make)
    map.update(stringRep, result)
    expressions.update(stringRep, result)
    result
  }

  //////////////////////////////////////////////////////////////////////////
  private def addProgramExpression[PE <: E with ProgramExpression, E <: Expression](
                                                                                     pMap: HashMap[String, PE],
                                                                                     map: HashMap[String, E],
                                                                                     stringRep: String,
                                                                                     make: => PE
                                                                                     ): PE = addSpecializedExpression[ProgramExpression, PE, E](pMap, map, stringRep, make)

  //////////////////////////////////////////////////////////////////////////
  private def addDomainExpression[DE <: E with DomainExpression, E <: Expression](
                                                                                   dMap: HashMap[String, DE],
                                                                                   map: HashMap[String, E],
                                                                                   stringRep: String,
                                                                                   make: => DE
                                                                                   ): DE = addSpecializedExpression[DomainExpression, DE, E](dMap, map, stringRep, make)

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val domainPredicates = new HashMap[String, DomainPredicate]

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val programTerms = new HashSet[ProgramTerm]
  private val domainTerms = new HashSet[DomainTerm]
  private val terms = new HashSet[Term]

  //////////////////////////////////////////////////////////////////////////
  private val dEqualityExpressions = new HashMap[String, DEqualityExpression]
  private val pEqualityExpressions = new HashMap[String, PEqualityExpression]
  private val equalityExpressions = new HashMap[String, EqualityExpression]

  private val dDomainPredicateExpressions = new HashMap[String, DDomainPredicateExpression]
  private val pDomainPredicateExpressions = new HashMap[String, PDomainPredicateExpression]
  private val domainPredicateExpressions = new HashMap[String, DomainPredicateExpression]

  private val dUnaryBooleanExpressions = new HashMap[String, DUnaryBooleanExpression]
  private val pUnaryBooleanExpressions = new HashMap[String, PUnaryBooleanExpression]
  private val unaryBooleanExpressions = new HashMap[String, UnaryBooleanExpression]

  private val dBinaryBooleanExpressions = new HashMap[String, DBinaryBooleanExpression]
  private val pBinaryBooleanExpressions = new HashMap[String, PBinaryBooleanExpression]
  private val binaryBooleanExpressions = new HashMap[String, BinaryBooleanExpression]

  private val accessPermissionExpressions = new HashMap[String, AccessPermissionExpression]
  private val unfoldingExpressions = new HashMap[String, UnfoldingExpression]

  private val pPredicateExpressions = new HashMap[String, PPredicateExpression]
  private val predicateExpressions = new HashMap[String, PredicateExpression]

  private val dQuantifierExpressions = new HashMap[String, DQuantifierExpression]
  private val quantifierExpressions = new HashMap[String, QuantifierExpression]

  private val expressions = new HashMap[String, Expression]

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


