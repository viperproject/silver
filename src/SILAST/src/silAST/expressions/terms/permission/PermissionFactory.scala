package silAST.expressions.terms.permission

import silAST.programs.NodeFactory
import silAST.source.SourceLocation
import collection.mutable.HashSet


trait PermissionFactory extends NodeFactory
{
  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermissionTerm() = FullPermissionTerm.fullPermissionTerm
  def makeNoPermissionTerm() = NoPermissionTerm.noPermissionTerm
  def makeEpsilonPermissionTerm() = EpsilonPermissionTerm.epsilonPermissionTerm

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermissionTerm(sl : SourceLocation, percentage : Int) : PercentagePermissionTerm = {
    require(percentage>0 && percentage < 100)
    val result = new PercentagePermissionTerm(sl,percentage)
    permissionTerms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionVariableTerm (sl : SourceLocation, variable : PermissionVariable)
  {
    require(permissionVariables contains variable)
    val result = new PermissionVariableTerm(sl,variable)
    permissionTerms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(sl : SourceLocation,t1 : PermissionTerm,t2 : PermissionTerm ) : PermissionAdditionTerm =
    makePermissionBinaryTerm(t1,t2,new PermissionAdditionTerm(sl,_,_))
  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(sl : SourceLocation,t1 : PermissionTerm,t2 : PermissionTerm ) : PermissionSubtractionTerm =
    makePermissionBinaryTerm(t1,t2,new PermissionSubtractionTerm(sl,_,_))
  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(sl : SourceLocation,t1 : PermissionTerm,t2 : PermissionTerm ) : PermissionMultiplicationTerm =
    makePermissionBinaryTerm(t1,t2,new PermissionMultiplicationTerm(sl,_,_))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(
    sl : SourceLocation,
    t1 : PermissionTerm,
    i : Int
  ) : PermissionIntegerMultiplicationTerm =
  {
    require(permissionTerms contains t1)
    val result = new PermissionIntegerMultiplicationTerm(sl,t1,i)
    permissionTerms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  private def makePermissionBinaryTerm[T <: PermissionTerm](
    t1 : PermissionTerm,
    t2 : PermissionTerm,
    c : (PermissionTerm,PermissionTerm) => T
  ) : T =
  {
    require(permissionTerms contains t1)
    require(permissionTerms contains t2)
    val result = c(t1,t2)
    permissionTerms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  protected[silAST] val permissionTerms = new HashSet[PermissionTerm]
  permissionTerms += FullPermissionTerm.fullPermissionTerm
  permissionTerms += NoPermissionTerm.noPermissionTerm
  permissionTerms += EpsilonPermissionTerm.epsilonPermissionTerm

  protected[silAST] val permissionVariables = new HashSet[PermissionVariable]
}