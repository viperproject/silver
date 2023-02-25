package viper.silver.plugin.standard.reasoning

import viper.silver.FastMessaging
import viper.silver.ast.{ErrorTrafo, ExtensionExp, Info, Label, LocalVar, LocalVarDecl, Member, Method, MethodCall, NoInfo, NoPosition, NoTrafos, Position, Seqn, SourcePosition, Stmt, Trigger}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PGlobalDeclaration, PIdnDef, PIdnUse, PLabel, PLocalVarDecl, PMember, PMethod, PNode, PSeqn, PStmt, PTrigger, PType, PTypeSubstitution, Translator, TypeChecker}
import viper.silver.plugin.standard.termination.PDecreasesClause

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
//sealed trait PFlowAnnotation extends PExtender with PExp {
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
/*
case class PFlowAnnotationVar(v:PExp, varList: Seq[PExp])(val pos: (Position,Position)) extends PFlowAnnotation {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
   varList.foreach(c => {
      t.checkTopTyped(c, None)
    })
    t.checkTopTyped(v, None)
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    FlowAnnotationVar(t.exp(v), varList.map { case variable => t.exp(variable) })(t.liftPos(this))

  }
}

/** specified type of the PFlowAnnotationVar class which includes heap as one of the argument variables */
case class PFlowAnnotationVarHeapArg(v:PExp, varList: Seq[PExp])(val pos:(Position,Position)) extends PFlowAnnotation {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {

    varList.foreach(c => {
      t.checkTopTyped(c, None)
    })
    t.checkTopTyped(v, None)
    None
  }
  override def translateExp(t: Translator): ExtensionExp = FlowAnnotationVarHeapArg(t.exp(v), varList.map { case variable => t.exp(variable) })(t.liftPos(this))
}

case class PFlowAnnotationHeap(varList: Seq[PExp])(val pos: (Position,Position)) extends PFlowAnnotation {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    varList.foreach(c => t.checkTopTyped(c, None))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    FlowAnnotationHeap(varList.map { case variable => t.exp(variable) })(t.liftPos(this))

  }
}

case class PFlowAnnotationHeapHeapArg(varList: Seq[PExp])(val pos: (Position,Position)) extends PFlowAnnotation {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    varList.foreach(c => t.checkTopTyped(c, None))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    FlowAnnotationHeapHeapArg(varList.map { case variable => t.exp(variable) })(t.liftPos(this))

  }
}

 */


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
  /*
  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    None
  }


  override def getSubnodes(): Seq[PNode] = method.subnodes

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(method)()
    None
  }

  override def idndef: PIdnDef = method.idndef

  override val pos: (Position, Position) = lemma_pos

  override def translateMember(t: Translator): Member = {
    //Lemma(Method(method.idndef.name,method.formalArgs map t.liftVarDecl,method.formalReturns map t.liftVarDecl,method.pres map t.exp,method.posts map t.exp,Option(Seqn(method.body)))(lemma_pos))
    val newBody = method.body.map(actualBody => {
      val b = t.stmt(actualBody).asInstanceOf[Seqn]
      val newScopedDecls = b.scopedSeqnDeclarations ++ b.deepCollect { case l: Label => l }

      b.copy(scopedSeqnDeclarations = newScopedDecls)(b.pos, b.info, b.errT)
    })

    val finalMethod = Method(pres = method.pres map t.exp, posts = method.posts map t.exp, body = newBody, formalArgs = method.formalArgs map t.liftVarDecl, formalReturns = method.formalReturns map t.liftVarDecl, name = method.idndef.name)(method.pos._1)

    t.getMembers().addOne(method.idndef.name, finalMethod)

    finalMethod
  }
  override def translateMemberSignature(t: Translator): Member = {
    Method(method.idndef.name, method.formalArgs map t.liftVarDecl, method.formalReturns map t.liftVarDecl, null, null, null)(method.pos._1)
  }
  */
}

case class POldCall(rets: Seq[PIdnUse], lbl:PIdnUse, method: PIdnUse, args:Seq[PExp])(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = rets ++ Seq(method) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    args.foreach(a =>
      t.checkTopTyped(a,None)
    )
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    //OldCall(rets.map(r => LocalVar(r.name, t.ttyp(r.typ))(t.liftPos(r))), Label(lbl.name, Seq() map t.exp)(t.liftPos(lbl)),t.exp(exp))(t.liftPos(this))
    OldCall(MethodCall(method.name, args map t.exp, rets.map(r => LocalVar(r.name,t.ttyp(r.typ))(t.liftPos(r))))(t.liftPos(method), NoInfo, NoTrafos), Label(lbl.name, Seq())(t.liftPos(lbl)))(t.liftPos(this))
  }
}