package silAST.programs

import silAST.expressions.terms.Term
import collection.mutable.HashSet

trait GTermFactory extends NodeFactory
{

  protected[silAST] val terms = new HashSet[Term]
}