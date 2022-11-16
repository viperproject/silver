package viper.silver.plugin.standard.reasoning

import viper.silver.ast.{LocalVarDecl, Position, Seqn, Stmt, Trigger}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PLocalVarDecl, PNode, PSeqn, PStmt, PTrigger, Translator, TypeChecker}

case class PExistentialElim(varList: Seq[PLocalVarDecl], trig: Seq[PTrigger], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = {
    varList ++ trig ++ Seq(e)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varList foreach (v => {
      t.check(v.typ)
    })
    trig foreach (_.exp foreach (tpe=>t.checkTopTyped(tpe,None)))
    t.check(e, Bool)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    ExistentialElim(varList.map { case variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable)) }, trig.map{case t1 => Trigger(t1.exp.map{ t2 => t.exp(t2)})(t.liftPos(t1))}, t.exp(e))(t.liftPos(e))
  }

}
case class PUniversalIntro(varList: Seq[PLocalVarDecl], triggers: Seq[PTrigger], e1: PExp, e2: PExp, block: PSeqn)(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = varList ++ triggers ++ Seq(e1) ++ Seq(e2) ++ Seq(block)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varList foreach (v => t.check(v.typ))
    triggers foreach (_.exp foreach (tpe=>t.checkTopTyped(tpe,None)))
    t.check(e1, Bool)
    t.check(e2, Bool)
    t.check(block)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    UniversalIntro(varList.map { case variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable))}, triggers.map{case t1 => Trigger(t1.exp.map{ t2 => t.exp(t2)})(t.liftPos(t1))}, t.exp(e1), t.exp(e2), Seqn(block.ss.map{blstmt => t.stmt(blstmt)}, Seq())(t.liftPos(block)))(t.liftPos(e1))
  }

}