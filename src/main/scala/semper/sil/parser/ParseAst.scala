package semper.sil.parser

import org.kiama.util.Positioned
import org.kiama.attribution.Attributable

/**
 * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
 * with the actual SIL abstract syntax tree.
 */
sealed trait PNode extends Positioned with Attributable

// Identifiers (uses and definitions)
trait Identifier
case class PIdnDef(name: String) extends PNode with Identifier
case class PIdnUse(name: String) extends PExp with Identifier

// Formal arguments
case class PFormalArgDecl(idndef: PIdnDef, typ: PType) extends PNode

// Types
sealed trait PType extends PNode
case class PPrimitiv(name: String) extends PType
case class PTypeVar(name: String) extends PType
case class PDomainType(domain: PIdnUse, args: Seq[PType]) extends PType
case class PUnkown() extends PType // for resolving if something cannot be typed

// Expressions
sealed trait PExp extends PNode
case class PBinExp(left: PExp, op: String, right: PExp) extends PExp
case class PUnExp(op: String, exp: PExp) extends PExp
case class PIntLit(i: BigInt) extends PExp
case class PThisLit() extends PExp
case class PResultLit() extends PExp
case class PBoolLit(b: Boolean) extends PExp
case class PFieldAcc(rcv: PExp, idnuse: PIdnUse) extends PExp

// Statements
sealed trait PStmt extends PNode {
  /**
   * Returns a list of all actual statements contained in this statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def childStmts: Seq[PStmt] = {
    this match {
      case PSeqn(ss) => ss
      case PIf(_, thn, els) => Seq(this, thn, els)
      case PWhile(_, _, body) => Seq(this, body)
      case _ => Seq(this)
    }
  }
}
case class PSeqn(ss: Seq[PStmt]) extends PStmt
case class PFold(e: PExp) extends PStmt
case class PUnfold(e: PExp) extends PStmt
case class PExhale(e: PExp) extends PStmt
case class PInhale(e: PExp) extends PStmt
case class PVarAssign(idnuse: PIdnUse, rhs: PExp) extends PStmt
case class PIf(cond: PExp, thn: PStmt, els: PStmt) extends PStmt
case class PWhile(cond: PExp, invs: Seq[PExp], stmt: PStmt) extends PStmt
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt

// Program
sealed trait PProgram extends PNode

// Method
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: PStmt) extends PNode

// Domain
sealed trait PDomain extends PNode
