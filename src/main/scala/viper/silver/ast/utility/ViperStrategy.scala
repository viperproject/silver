package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._
import viper.silver.ast.utility.Rewriter.Traverse.Traverse
import viper.silver.verifier.errors.ErrorNode

/**
  * Created by simonfri on 24.01.2017.
  */
class ViperStrategy[C <: Context[Node]](p: PartialFunction[(Node, C), Node]) extends Strategy[Node, C](p) {
  override def preserveMetaData(old: Node, now: Node): Node = {
    old match {
      case n:TransformableErrors => {
        val OldMetaData = old.getPrettyMetadata
        var NewMetaData = now.getPrettyMetadata

        if((NewMetaData._1 eq NoPosition) && (NewMetaData._2 eq NoInfo) && (NewMetaData._3 eq NoTrafos)) {
          NewMetaData = (OldMetaData._1, OldMetaData._2, OldMetaData._3)
        }

        // Only duplicate if old and new are actually different
        if(old ne now) {
          NewMetaData = (NewMetaData._1, NewMetaData._2, NewMetaData._3 ++ NodeTrafo({ case _ => n.asInstanceOf[ErrorNode] }))
          transformed(now.duplicateMeta(NewMetaData))
        } else {
          now
        }
      }
      case _ => now
    }
  }
}

object ViperStrategy {
  def Slim(p: PartialFunction[Node, Node]) = {
    new ViperStrategy[SimpleContext[Node]](AddArtificialContext(p)) defaultContext new NoContext[Node]
  }

  def Ancestor(p: PartialFunction[(Node, ContextA[Node]), Node], t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[ContextA[Node]](p) defaultContext new PartialContextA[Node] traverse t
  }

  def Context[C](p: PartialFunction[(Node, ContextC[Node, C]), Node], default: C, updateFunc: PartialFunction[(Node, C), C] = PartialFunction.empty, t:Traverse = Traverse.TopDown) = {
    new ViperStrategy[ContextC[Node, C]](p) defaultContext new PartialContextC[Node, C](default, updateFunc) traverse t
  }
}
