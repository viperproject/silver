package viper.silver.plugin.standard.reasoning

import viper.silver.ast.{ExtensionExp, Label, LocalVar, LocalVarDecl, Position, Seqn, Stmt, Trigger}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PIdnUse, PLocalVarDecl, PNode, PSeqn, PStmt, PTrigger, PType, PTypeSubstitution, Translator, TypeChecker}

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
    val res = UniversalIntro(varList.map { case variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable))}, triggers.map{case t1 => Trigger(t1.exp.map{ t2 => t.exp(t2)})(t.liftPos(t1))}, t.exp(e1), t.exp(e2), t.stmt(block).asInstanceOf[Seqn])(t.liftPos(e1))
    res
  }

}

case class PFlowAnnotation(v:PFlowVar, varList: Seq[PFlowVar])(val pos: (Position,Position)) extends PExtender with PExp {
  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override val getSubnodes: Seq[PNode] = Seq()

  //from here new
  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {

    varList.foreach(c => {
      if (c.isInstanceOf[PVar]) {
        t.checkTopTyped(c.asInstanceOf[PVar].var_decl, None)
      }
    })
    if (v.isInstanceOf[PVar]) {
      t.checkTopTyped(v.asInstanceOf[PVar].var_decl, None)
    }


    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
  FlowAnnotation(v.translate(t), varList.map { case variable => variable.translate(t) })(t.liftPos(this))

  }
}
sealed trait PFlowVar extends PNode {

  def translate(t:Translator): FlowVar
}

case class PHeap()(val pos: (Position,Position)) extends PFlowVar {
  override def translate(t:Translator): Heap = {
    Heap()(t.liftPos(this))
  }
}

case class PVar(decl:PExp)(val pos: (Position,Position)) extends PFlowVar{
  def var_decl:PExp = decl

  override def translate(t:Translator): Var = {
    Var(t.exp(decl))(t.liftPos(this))
  }
}

case class PLemma()(val pos: (Position,Position)) extends PExtender with PExp {

  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override val getSubnodes: Seq[PNode] = Seq()

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    Lemma()(t.liftPos(this))

  }
}

case class POldCall(rets: Seq[PIdnUse], lbl:PIdnUse, method: PIdnUse, args:Seq[PExp])(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = rets ++ Seq(method) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    args.foreach(a =>
      t.checkTopTyped(a,None)
    )
    rets.foreach(r =>
      t.checkTopTyped(r, None))
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    OldCall(method.name, args map t.exp, (rets map t.exp).asInstanceOf[Seq[LocalVar]], Label(lbl.name, Seq())(t.liftPos(lbl)))(t.liftPos(this))

  }
}