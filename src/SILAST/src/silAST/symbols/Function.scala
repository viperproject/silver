package silAST.symbols

import silAST.ASTNode

abstract class Function extends ASTNode {
  val name: String
  val signature: FunctionSignature
}