package viper.silver.plugin.standard.reasoning

import viper.silver.ast.{LocalVarDecl, Position, Stmt}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PLocalVarDecl, PNode, PStmt, PTrigger, PType, Translator, TypeChecker}

//case class PExistentialElim(varList: Seq[(PIdnDef, PType)], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {

// version without local var decl in out obtain statement
case class PExistentialElim(varList: Seq[(String, PType)], t: Seq[PTrigger], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = {
    Seq(e)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varList foreach (v => scala.Console.println("local var name = " + v._1))
    t.check(e, Bool)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    scala.Console.println("entered translateStmt!")
    ExistentialElim(varList.map{case (id, typ) => LocalVarDecl(id, t.ttyp(typ))(t.liftPos(e))}, t.exp(e))(t.liftPos(e))
  }
}


// version with local var decl in our obtain statement
/*
case class PExistentialElim(varList: Seq[PLocalVarDecl], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = {
    //varList ++ Seq(e)
    varList ++ Seq(e)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varList foreach (v => scala.Console.println("local var name = " + v.idndef.name))
    varList foreach {
      //v => n.namesInScope(v, Some(this))
      v => t.check(v)
    }
    t.check(e, Bool)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    scala.Console.println("entered translateStmt!")
    ExistentialElim(varList.map { case variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable)) }, t.exp(e))(t.liftPos(e))
  }

  //override def translateStmt(t: Translator): Stmt = ExistentialElim(varList.map{ case (id, typ) => LocalVarDecl(id.name, t.ttyp(typ))(t.liftPos(id))} ,t.exp(e))(t.liftPos(this))
  //LocalVarDecl(varList.name, t.ttyp(typ))(t.liftPos(id))
}
 */
/*
case class PExistentialElim(lvd:PFormalArgDecl, e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {
  override val getSubnodes: Seq[PNode] = Seq(e)

}
*/